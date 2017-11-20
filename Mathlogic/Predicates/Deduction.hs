module Mathlogic.Predicates.Deduction where

import Mathlogic.Predicates.Parser
import Mathlogic.Predicates.Axioms
import Mathlogic.Predicates.Checker (Wrong(..))

import qualified Data.Set as DS
import Data.List (find, foldl')
import Data.Maybe(fromJust)

aaLemm :: Expression -> Proof
aaLemm a = [ Implication a a
           , Implication a (Implication (Implication a a) a)
           , Implication (Implication a (Implication (Implication a a) a)) (Implication a a)
           , Implication (Implication a (Implication a a)) (Implication (Implication a (Implication (Implication a a) a)) (Implication a a))
           , Implication a (Implication a a) ]

simpleTruth a b = [ Implication b a
                  , Implication a (Implication b a)
                  , a ]

produce :: File4 -> Either Wrong File4
produce (File4 (Hdr preps exp) proof) = (foldl' magic (Right []) (zip [1..] proof)) >>=
                                        (Right . reverse) >>=
                                        (Right . File4 (Hdr (initPreps) (Implication lastPrep exp))) where
    initPreps = init preps
    lastPrep  = last preps
    bad = freeVariables lastPrep
    magic :: Either Wrong Proof -> (Int, Expression) -> Either Wrong Proof
    magic err@(Left _) _ = err
    magic (Right builtProof) (expNo, curExp)
        | curExp == lastPrep              = Right $ aaLemm curExp ++ builtProof
        | checkPrepositions curExp        = Right $ simpleTruth curExp lastPrep ++ builtProof
        | checkAxioms curExp == Nothing   = Right $ simpleTruth curExp lastPrep ++ builtProof -- means IS an axiom
        | checkMP expNo curExp /= Nothing = Right $ makeMPProof (fromJust $ checkMP expNo curExp) curExp ++ builtProof
    checkPrepositions e = any ((==) e) preps
    checkAxioms e = case getMathedAxiom e of
        Left (Bounded var sub e2) -> Just $ BoundedVariable var sub e2
        Left NotAnAxiom           -> Just Bad
        Right _                   -> Nothing
    checkMP :: Int -> Expression -> Maybe Expression -- checkMP n a = Just b for b -> a and b
    checkMP no t = find fimpt (take (no-1) proof) >>= \(Implication x _) -> find (== x) (take (no-1) proof) where
        fimpt (Implication from to) = to == t
        fimpt _ = False
    makeMPProof f t = [ Implication lastPrep t
                      , Implication (Implication lastPrep (Implication f t)) (Implication lastPrep t)
                      , Implication (Implication lastPrep f) (Implication (Implication lastPrep (Implication f t)) (Implication lastPrep t)) ]
