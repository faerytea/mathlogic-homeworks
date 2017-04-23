module Mathlogic.Predicate.Checker where

import Mathlogic.Predicates.Parser
import Mathlogic.Predicates.Axioms
import qualified Data.Set as DS
import Data.Maybe(fromJust)

data Wrong = Bad                                      -- just doesn't proved
           | BoundedVariable String String Expression -- term X is not free for substitution (ax.11, ax.12)
           | FreeVariable String Expression           -- variable is free (rules)
           | BadUsageRule String Expression           -- presented in preposition (rules)
           | BadUsageScheme String Expression         -- presented in preposition (axioms)
           deriving (Show, Eq)

process :: (a -> Maybe b) -> [a] -> Maybe b
process _ []     = Nothing
process f (x:xs) = case f x of
    Nothing  -> process f xs
    Just res -> Just res

checkProof :: File4 -> Maybe (Int, Wrong)
checkProof (File4 (Hdr preps exp) proof) = process checks $ zip [1..] proof where
    lastPrep = last preps
    bad = freeVariables lastPrep
    checks e@(n, _)
        | checkPrepositions e           = Nothing
        | checkAxioms e     == Nothing  = Nothing
        | checkAnyRule e    == Nothing  = Nothing
        | checkExistsRule e == Nothing  = Nothing
        | checkMP e                     = Nothing -- last MP check, will not be correct further ofc
        | checkAxioms e     /= Just Bad = Just (n, fromJust $ checkAxioms e)
        | checkAnyRule e    /= Just Bad = Just (n, fromJust $ checkAnyRule e)
        | checkExistsRule e /= Just Bad = Just (n, fromJust $ checkExistsRule e)
        | otherwise                     = Just (n, Bad)
    checkAnyRule (n, (Implication phi (Quantifier All var psi)))
        | DS.member var bad                 = Just $ BadUsageRule var lastPrep
        | DS.member var $ freeVariables phi = Just $ FreeVariable var phi
        | otherwise                         = case process (\e -> if e == (Implication phi psi) then Just True else Nothing) $ take (n - 1) proof of
                                                  Just _  -> Nothing
                                                  Nothing -> Just Bad
    checkAnyRule _ = Just Bad
    checkExistsRule (n, (Implication (Quantifier Ex var psi) phi))
        | DS.member var bad                 = Just $ BadUsageRule var lastPrep
        | DS.member var $ freeVariables phi = Just $ FreeVariable var phi
        | otherwise                         = case process (\e -> if e == (Implication psi phi) then Just True else Nothing) $ take (n - 1) proof of
                                                  Just _  -> Nothing
                                                  Nothing -> Just Bad
    checkExistsRule _ = Just Bad
    checkPrepositions (_, e) = any ((==) e) preps
    checkAxioms (_, e) = case getMathedAxiom e of
        Left (Bounded var sub e2) -> Just $ BoundedVariable var sub e2
        Left NotAnAxiom           -> Just Bad
        Right _                   -> Nothing -- BadUsageScheme?
    checkMP (n, e) = Nothing /= (process magic $ take (n-1) $ zip [1..] proof) where
        magic (_, Implication a b) = if b /= e then Nothing
                                               else process (\z -> if z == a then Just True else Nothing) $ take (n-1) proof
        magic _                    = Nothing
