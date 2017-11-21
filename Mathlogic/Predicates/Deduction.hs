module Mathlogic.Predicates.Deduction where

import Mathlogic.Predicates.Parser
import Mathlogic.Predicates.Axioms
import Mathlogic.Predicates.Checker (Wrong(..))

import qualified Data.Set as DS
import qualified Data.Map as DM
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

substitute:: DM.Map String Expression -> DM.Map String String -> Expression -> Expression
substitute me mv expr = go expr where
    fwd = DM.findWithDefault
    go (Implication a b) = Implication (go a) (go b)
    go (Conjunction a b) = Conjunction (go a) (go b)
    go (Disjunction a b) = Disjunction (go a) (go b)
    go (Not a) = Not (go a)
    go (Predicate a vars) = Predicate a (map got vars)
    go s@(Scheme a) = fwd s a me
    go (Quantifier q v e) = Quantifier q (fwd v v mv) (go e)
    got (Sum a b) = Sum (got a) (got b)
    got (Production a b) = Production (got a) (got b)
    got (Function n ts) = Function n (map got ts)
    got (Var n) = Var (fwd n n mv)
    got Zero = Zero
    got (Hatch t) = Hatch (got t)

produce :: File4 -> Either (Int, Wrong) File4
produce (File4 (Hdr preps exp) proof) = (foldl' magic (Right []) (zip [1..] proof)) >>=
                                        (Right . reverse) >>=
                                        (Right . File4 (Hdr (initPreps) (Implication lastPrep exp))) where
    initPreps = init preps
    lastPrep  = last preps
    bad = freeVariables lastPrep
    magic :: Either (Int, Wrong) Proof -> (Int, Expression) -> Either (Int, Wrong) Proof
    magic err@(Left _) _ = err
    magic (Right builtProof) (expNo, curExp)
        | curExp == lastPrep                       = Right $ aaLemm curExp ++ builtProof
        | checkPrepositions curExp                 = Right $ simpleTruth curExp lastPrep ++ builtProof
        | checkAxioms curExp == Nothing            = Right $ simpleTruth curExp lastPrep ++ builtProof -- means IS an axiom
        | checkAnyRule expNo curExp    == Nothing  = Right $ makeAllProof curExp ++ builtProof
        | checkExistsRule expNo curExp == Nothing  = Right $ makeExProof curExp ++ builtProof
        | checkMP expNo curExp /= Nothing          = Right $ makeMPProof (fromJust $ checkMP expNo curExp) curExp ++ builtProof
        | checkAxioms curExp           /= Just Bad = Left (expNo, fromJust $ checkAxioms curExp)
        | checkAnyRule expNo curExp    /= Just Bad = Left (expNo, fromJust $ checkAnyRule expNo curExp)
        | checkExistsRule expNo curExp /= Just Bad = Left (expNo, fromJust $ checkExistsRule expNo curExp)
        | otherwise                                = Left (expNo, Bad)
    checkPrepositions e = any ((==) e) preps
    -- checkBadAxiomUsage var be = if var `DS.member` bad then Just (BadUsageScheme var be) else Nothing
    checkAxioms e = case getMathedAxiom e of
        Left (Bounded var sub e2) -> Just $ BoundedVariable var sub e2
        Left NotAnAxiom           -> Just Bad
        -- Right (11, _)             -> let be@(Implication q@(Quantifier All var psi) spsi) = e in checkBadAxiomUsage var be
        -- Right (12, _)             -> let be@(Implication spsi q@(Quantifier Ex var psi))  = e in checkBadAxiomUsage var be
        Right _                   -> Nothing
    checkMP :: Int -> Expression -> Maybe Expression -- checkMP n a = Just b for b -> a and b
    checkMP no t = mHead $ filter fimpt (take (no-1) proof) >>= \(Implication x _) -> filter (== x) (take (no-1) proof) where
        fimpt (Implication from to) = to == t
        fimpt _ = False
        mHead [] = Nothing
        mHead (x:_) = Just x
    makeMPProof f t = [ Implication lastPrep t
                      , Implication (Implication lastPrep (Implication f t)) (Implication lastPrep t)
                      , Implication (Implication lastPrep f) (Implication (Implication lastPrep (Implication f t)) (Implication lastPrep t)) ]
    makeQProof l r v = map (substitute (DM.fromList [("A", lastPrep), ("B", l), ("C", r)]) (DM.singleton "x" v))
    checkExistsRule n (Implication (Quantifier Ex var psi) phi)
        | DS.member var bad                 = Just $ BadUsageRule var lastPrep
        | DS.member var $ freeVariables phi = Just $ FreeVariable var phi
        | otherwise                         = if any (== Implication psi phi) $ take (n - 1) proof then Nothing else Just Bad
    checkExistsRule _ _ = Just Bad
    makeExProof (Implication (Quantifier Ex v l) r) = makeQProof l r v exProof
    checkAnyRule n (Implication phi (Quantifier All var psi))
        | DS.member var bad                 = Just $ BadUsageRule var lastPrep
        | DS.member var $ freeVariables phi = Just $ FreeVariable var phi
        | otherwise                         = if any (== Implication phi psi) $ take (n - 1) proof then Nothing else Just Bad
    checkAnyRule _ _ = Just Bad
    makeAllProof (Implication l (Quantifier All v r)) = makeQProof l r v allProof
    exProof = reverse $ map parseExpression [ "~B->~A->~B",
                                              "~A->~B->~C",
                                              "(~A->~B->~C)->~B->~A->~B->~C",
                                              "~B->~A->~B->~C",
                                              "(~A->~B)->(~A->~B->~C)->~A->~C",
                                              "((~A->~B)->(~A->~B->~C)->~A->~C)->~B->(~A->~B)->(~A->~B->~C)->~A->~C",
                                              "~B->(~A->~B)->(~A->~B->~C)->~A->~C",
                                              "(~B->~A->~B)->(~B->(~A->~B)->(~A->~B->~C)->~A->~C)->~B->(~A->~B->~C)->~A->~C",
                                              "(~B->(~A->~B)->(~A->~B->~C)->~A->~C)->~B->(~A->~B->~C)->~A->~C",
                                              "~B->(~A->~B->~C)->~A->~C",
                                              "(~B->~A->~B->~C)->(~B->(~A->~B->~C)->~A->~C)->~B->~A->~C",
                                              "(~B->(~A->~B->~C)->~A->~C)->~B->~A->~C",
                                              "~B->~A->~C",
                                              "?x~B->~A->~C",
                                              "~A->?x~B->~A",
                                              "?x~B->~A->~C",
                                              "(?x~B->~A->~C)->~A->?x~B->~A->~C",
                                              "~A->?x~B->~A->~C",
                                              "(?x~B->~A)->(?x~B->~A->~C)->?x~B->~C",
                                              "((?x~B->~A)->(?x~B->~A->~C)->?x~B->~C)->~A->(?x~B->~A)->(?x~B->~A->~C)->?x~B->~C",
                                              "~A->(?x~B->~A)->(?x~B->~A->~C)->?x~B->~C",
                                              "(~A->?x~B->~A)->(~A->(?x~B->~A)->(?x~B->~A->~C)->?x~B->~C)->~A->(?x~B->~A->~C)->?x~B->~C",
                                              "(~A->(?x~B->~A)->(?x~B->~A->~C)->?x~B->~C)->~A->(?x~B->~A->~C)->?x~B->~C",
                                              "~A->(?x~B->~A->~C)->?x~B->~C",
                                              "(~A->?x~B->~A->~C)->(~A->(?x~B->~A->~C)->?x~B->~C)->~A->?x~B->~C",
                                              "(~A->(?x~B->~A->~C)->?x~B->~C)->~A->?x~B->~C",
                                              "~A->?x~B->~C" ]
    allProof = reverse $ map parseExpression [ "~A->~B->~C",
                                               "~A&~B->~A",
                                               "~A&~B->~B",
                                               "(~A->~B->~C)->~A&~B->~A->~B->~C",
                                               "~A&~B->~A->~B->~C",
                                               "(~A&~B->~A)->(~A&~B->~A->~B->~C)->~A&~B->~B->~C",
                                               "(~A&~B->~A->~B->~C)->~A&~B->~B->~C",
                                               "~A&~B->~B->~C",
                                               "(~A&~B->~B)->(~A&~B->~B->~C)->(~A&~B->~C)",
                                               "(~A&~B->~B->~C)->(~A&~B->~C)",
                                               "~A&~B->~C",
                                               "~A&~B->@x~C",
                                               "~A->~B->~A&~B",
                                               "(~A&~B->@x~C)->~A->~A&~B->@x~C",
                                               "~A->~A&~B->@x~C",
                                               "(~A&~B->@x~C)->~B->~A&~B->@x~C",
                                               "((~A&~B->@x~C)->~B->~A&~B->@x~C)->~A->(~A&~B->@x~C)->~B->~A&~B->@x~C",
                                               "~A->(~A&~B->@x~C)->~B->~A&~B->@x~C",
                                               "(~A->~A&~B->@x~C)->(~A->((~A&~B->@x~C)->~B->~A&~B->@x~C))->~A->~B->~A&~B->@x~C",
                                               "(~A->((~A&~B->@x~C)->~B->~A&~B->@x~C))->~A->~B->~A&~B->@x~C",
                                               "~A->~B->~A&~B->@x~C",
                                               "(~B->~A&~B)->(~B->~A&~B->@x~C)->~B->@x~C",
                                               "((~B->~A&~B)->(~B->~A&~B->@x~C)->~B->@x~C)->~A->(~B->~A&~B)->(~B->~A&~B->@x~C)->~B->@x~C",
                                               "~A->(~B->~A&~B)->(~B->~A&~B->@x~C)->~B->@x~C",
                                               "(~A->~B->~A&~B)->(~A->(~B->~A&~B)->(~B->~A&~B->@x~C)->~B->@x~C)->~A->(~B->~A&~B->@x~C)->~B->@x~C",
                                               "(~A->(~B->~A&~B)->(~B->~A&~B->@x~C)->~B->@x~C)->~A->(~B->~A&~B->@x~C)->~B->@x~C",
                                               "~A->(~B->~A&~B->@x~C)->~B->@x~C",
                                               "(~A->~B->~A&~B->@x~C)->(~A->(~B->~A&~B->@x~C)->~B->@x~C)->~A->~B->@x~C",
                                               "(~A->(~B->~A&~B->@x~C)->~B->@x~C)->~A->~B->@x~C",
                                               "~A->~B->@x~C" ]
