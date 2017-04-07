module Mathlogic.Proof where

import Mathlogic
import Mathlogic.Parser
import Mathlogic.Deduction
import qualified Data.Set as DS
import qualified Data.Map.Strict as DM
import qualified Data.Sequence as S
import Data.Foldable(toList)
import Data.List(sortBy, find)
import Data.Maybe(fromJust)
import Data.Either

type Value = (DS.Set String, DS.Set String)

extract :: String -> Value -> (Token, Bool)
extract name (trueSet, falseSet) = case (DS.member name trueSet, DS.member name falseSet) of 
                                        (False, True)  -> (Not $ Token $ PVar name, False)
                                        (True, False)  -> (Token $ PVar name, True)
                                        (False, False) -> (Token $ PVar name, True)
                                        (True, True)   -> error ((show name) ++ " true and false at same time!");

-- generateProof :: Expression -> Either Value File12
-- generateProof exp = case generateTrivialProof (collectPVars exp, DS.empty) exp of 
    -- Left err   -> Left err
    -- Right good -> incrementalGenerator good where
        -- incrementalGenerator f12@(File12 (Hdr pp exp) _)
            -- | pp == []  = Right f12
            -- | otherwise = case excludePreposition f12 of
                -- Left val   -> Left val
                -- Right next -> incrementalGenerator next

extractAllPrepositions :: File12 -> File12
extractAllPrepositions f@(File12 (Hdr [] _) _) = f
extractAllPrepositions f = extractAllPrepositions $ extractPreposition f

generateProof :: Expression -> Either Value File12
generateProof e = if null wrongPrepositions then Right $ File12 (Hdr [] e) (Proof result)
                                            else fromJust wrongPrepositions
      where
        variants :: [Value]
        variants = genVariants $ toList $ collectPVars e
        genVariants []      = [(DS.empty, DS.empty)]
        genVariants (v:lst) = (map (\(t, f) -> (DS.insert v t, f)) (genVariants lst)) ++
                                (map (\(t, f) -> (t, DS.insert v f)) (genVariants lst))
        trivialProofs :: [Either Value File12]
        trivialProofs = map (\v -> generateTrivialProof v e) variants
        wrongPrepositions :: Maybe (Either Value File12)
        wrongPrepositions = find isLeft trivialProofs
        proveA :: Expression -> Expression -> [Expression]
        proveA p a = substituteProof (DM.fromList [("P", p), ("A", a)]) (map (decompose . parseExpression) [
            "(P->A)->(!P->A)->(P|!P)->A",
            "(!P->A)->(P|!P)->A",
            "(P|!P)->A",
            "A"])
        excluded :: [Expression]
        excluded = concat $ map (\v -> substituteProof (DM.singleton "A" $ makeExpression $ Token $ PVar v) excludedThird) $ toList $ collectPVars e
        genExpVariants :: [String] -> [Expression] -> [Expression]
        genExpVariants []     exps = exps
        genExpVariants (v:vs) exps = genExpVariants vs $
                                        (map (\exp -> Implication (Ad $ Ac $ Token $ PVar v) exp) exps) ++
                                        (map (\exp -> Implication (Ad $ Ac $ Not $ Token $ PVar v) exp) exps)
        pVars :: [String]
        pVars = DS.toAscList $ collectPVars e
        genFinalProofs :: [String] -> [Expression]
        genFinalProofs (p:[]) = proveA (makeExpression $ Token $ PVar p) e
        genFinalProofs (p:ps) = (concat $ map (proveA (makeExpression $ Token $ PVar p)) $ genExpVariants (reverse ps) [e]) ++
                                (genFinalProofs ps)
        result = excluded ++ (concat $ map (getProofFromFile12 . extractAllPrepositions) $ rights trivialProofs) ++ (genFinalProofs pVars)

 -- A|-!!A
doubleNot :: [Expression]
doubleNot = map parseExpression [
        "A->!A->A",
        "!A->A",
        "!A->!A->!A",
        "(!A->!A->!A)->(!A->(!A->!A)->!A)->(!A->!A)",
        "(!A->(!A->!A)->!A)->(!A->!A)",
        "!A->(!A->!A)->!A",
        "!A->!A",
        "(!A->A)->(!A->!A)->!!A",
        "(!A->!A)->!!A",
        "!!A"]

trueAndTrue = map parseExpression [
        "A->B->A&B",
        "B->A&B",
        "A&B"]  

falseAndTrue = map parseExpression [
        "!A->A&B->!A",
        "A&B->!A",
        "A&B->A",
        "(A&B->A)->(A&B->!A)->!(A&B)",
        "(A&B->!A)->!(A&B)",
        "!(A&B)"]

trueAndFalse = map parseExpression [
        "!B->A&B->!B",
        "A&B->!B",
        "A&B->B",
        "(A&B->B)->(A&B->!B)->!(A&B)",
        "(A&B->!B)->!(A&B)",
        "!(A&B)"]
        
falseAndFalse = trueAndFalse -- same

trueOrTrue = map parseExpression [
        "A->A|B",
        "A|B"]

trueOrFalse = trueOrTrue

falseOrTrue = map parseExpression [
        "B->A|B",
        "A|B"]

falseOrFalse = map parseExpression [
        "(A|B->A)->(A|B->!A)->!(A|B)",
        "(A->A)->(B->A)->(A|B->A)",
        "A->A->A",
        "(A->A->A)->(A->(A->A)->A)->(A->A)",
        "(A->(A->A)->A)->(A->A)",
        "A->(A->A)->A",
        "A->A",
        "(B->A)->(A|B->A)",
        "(B->!A->B)->B->(B->!A->B)",
        "B->!A->B",
        "B->(B->!A->B)",
        "B->B->B",
        "(B->B->B)->(B->(B->B)->B)->(B->B)",
        "(B->(B->B)->B)->(B->B)",
        "B->(B->B)->B",
        "B->B",
        "(B->B)->(B->B->(!A->B))->(B->(!A->B))",
        "(B->B->!A->B)->(B->!A->B)",
        "B->!A->B",
        "(!B->!A->!B)->B->(!B->!A->!B)",
        "!B->!A->!B",
        "B->!B->!A->!B",
        "!B->B->!B",
        "B->!B",
        "(B->!B)->(B->!B->!A->!B)->(B->!A->!B)",
        "(B->!B->!A->!B)->(B->!A->!B)",
        "B->!A->!B",
        "((!A->B)->(!A->!B)->!!A)->B->((!A->B)->(!A->!B)->!!A)",
        "(!A->B)->(!A->!B)->!!A",
        "B->((!A->B)->(!A->!B)->!!A)",
        "(B->(!A->B))->(B->(!A->B)->((!A->!B)->!!A))->(B->((!A->!B)->!!A))",
        "(B->((!A->B)->((!A->!B)->!!A)))->(B->((!A->!B)->!!A))",
        "B->((!A->!B)->!!A)",
        "(B->(!A->!B))->(B->(!A->!B)->!!A)->(B->!!A)",
        "(B->((!A->!B)->!!A))->(B->!!A))",
        "B->!!A",
        "(!!A->A)->B->(!!A->A)",
        "!!A->A",
        "B->!!A->A",
        "(B->!!A)->(B->!!A->A)->(B->A)",
        "(B->!!A->A)->(B->A)",
        "B->A",
        "A|B->A",
        "(A|B->!A)->!(A|B)",
        "!A->A|B->!A",
        "A|B->!A",
        "!(A|B)"]

trueMeansTrue = map parseExpression [
        "B->A->B",
        "A->B"]

falseMeansTrue = trueMeansTrue

falseMeansFalse = map parseExpression [
        "(A->!B->A)->A->(A->!B->A)",
        "(A->!B->A)",
        "A->(A->!B->A)",
        "A->A->A",
        "(A->A->A)->(A->(A->A)->A)->(A->A)",
        "(A->(A->A)->A)->(A->A)",
        "A->(A->A)->A",
        "A->A",
        "(A->A)->(A->A->(!B->A))->(A->(!B->A))",
        "(A->A->!B->A)->(A->!B->A)",
        "A->!B->A",
        "(!A->!B->!A)->A->(!A->!B->!A)",
        "!A->!B->!A",
        "A->!A->!B->!A",
        "!A->A->!A",
        "A->!A",
        "(A->!A)->(A->!A->!B->!A)->(A->!B->!A)",
        "(A->!A->!B->!A)->(A->!B->!A)",
        "A->!B->!A",
        "((!B->A)->(!B->!A)->!!B)->A->((!B->A)->(!B->!A)->!!B)",
        "(!B->A)->(!B->!A)->!!B",
        "A->((!B->A)->(!B->!A)->!!B)",
        "(A->(!B->A))->(A->(!B->A)->((!B->!A)->!!B))->(A->((!B->!A)->!!B))",
        "(A->((!B->A)->((!B->!A)->!!B)))->(A->((!B->!A)->!!B))",
        "A->((!B->!A)->!!B)",
        "(A->(!B->!A))->(A->(!B->!A)->!!B)->(A->!!B)",
        "(A->((!B->!A)->!!B))->(A->!!B)",
        "A->!!B",
        "(!!B->B)->A->(!!B->B)",
        "!!B->B",
        "A->!!B->B",
        "(A->!!B)->(A->!!B->B)->(A->B)",
        "(A->!!B->B)->(A->B)",
        "A->B"]

trueMeansFalse = map parseExpression [
        "A->(A->B)->A",
        "(A->B)->A",
        "((A->B)->A)->((A->B)->A->B)->((A->B)->B)",
        "((A->B)->A->B)->((A->B)->B)",
        "((A->B)->A)->((A->B)->A->(A->B))->((A->B)->A->B)",
        "((A->B)->A->(A->B))->((A->B)->A->B)",
        "(A->B)->A->(A->B)",
        "(A->B)->A->B",
        "(A->B)->B",
        "((A->B)->B)->((A->B)->!B)->!(A->B)",
        "((A->B)->!B)->!(A->B)",
        "!B->(A->B)->!B",
        "(A->B)->!B",
        "!(A->B)"]
        
contraposition = getProof $ 
                 extractPreposition $
                 extractPreposition $
                 File12 (Hdr (map parseExpression [ "A->B", "!B" ]) $ parseExpression "!A") $ Proof $ map parseExpression [
                     "(A->B)->(A->!B)->!A",
                     "A->B",
                     "(A->!B)->!A",
                     "!B->A->!B",
                     "!B",
                     "A->!B",
                     "!A"] where
                         getProof (File12 _ (Proof p)) = simplifyProof p

excludedThird = simplifyProof $
                foldr (++) [] $
                [
                    map parseExpression ["A->A|!A"],
                    substituteProof (DM.fromList [
                                                    ("A", parseExpression "A"),
                                                    ("B", parseExpression "A|!A")
                                                 ]) contraposition,
                    map parseExpression ["!(A|!A)->!A", "!A->A|!A"],
                    substituteProof (DM.fromList [
                                                    ("A", parseExpression "!A"),
                                                    ("B", parseExpression "A|!A")
                                                 ]) contraposition,
                    map parseExpression [
                        "!(A|!A)->!!A", 
                        "(!(A|!A)->!A)->(!(A|!A)->!!A)->!!(A|!A)",
                        "(!(A|!A)->!!A)->!!(A|!A)",
                        "!!(A|!A)",
                        "!!(A|!A)->A|!A",
                        "A|!A"]
                ]

generateTrivialProof :: Value -> Expression -> Either Value File12
generateTrivialProof valuesPair@(trueSet, falseSet) exp 
    | (snd trivialProof) && ((decompose exp) == (slast $ fst trivialProof)) = Right $ File12 (Hdr prepositions exp) (Proof preparedTrivialProof)
    | otherwise                                                             = Left valuesPair where
        prepositions = map (\x -> makeExpression $ (if x `DS.member` trueSet then id else Not) $ Token $ PVar x) (DS.toAscList $ DS.union trueSet falseSet)
        slast :: S.Seq a -> a
        slast s = S.index s ((S.length s) - 1)
        preparedTrivialProof = toList $ fst trivialProof
        trivialProof = mapFMT up1 up2 leafUp $ fakeWrap exp
        up1 (FakeT (Not t)) (proof, True)  = (foldl (S.|>) proof $ substituteProof (DM.singleton "A" $ makeExpression t) doubleNot, False)
        up1 (FakeT (Not _)) (proof, False) = (proof, True)
        up1 _ s                            = s
        -- And
        up2 (FakeC (And a b)) (pa, True) (pb, True)           = genericUp2 a b pa pb trueAndTrue   True
        up2 (FakeC (And a b)) (pa, False) (pb, True)          = genericUp2 a b pa pb falseAndTrue  False
        up2 (FakeC (And a b)) (pa, True) (pb, False)          = genericUp2 a b pa pb trueAndFalse  False
        up2 (FakeC (And a b)) (pa, False) (pb, False)         = genericUp2 a b pa pb falseAndFalse False
        -- Or
        up2 (FakeD (Or a b)) (pa, True) (pb, True)            = genericUp2 a b pa pb trueOrTrue   True
        up2 (FakeD (Or a b)) (pa, False) (pb, True)           = genericUp2 a b pa pb falseOrTrue  True
        up2 (FakeD (Or a b)) (pa, True) (pb, False)           = genericUp2 a b pa pb trueOrFalse  True
        up2 (FakeD (Or a b)) (pa, False) (pb, False)          = genericUp2 a b pa pb falseOrFalse False
        -- ->
        up2 (FakeE (Implication a b)) (pa, True) (pb, True)   = genericUp2 a b pa pb trueMeansTrue   True
        up2 (FakeE (Implication a b)) (pa, False) (pb, True)  = genericUp2 a b pa pb falseMeansTrue  True
        up2 (FakeE (Implication a b)) (pa, True) (pb, False)  = genericUp2 a b pa pb trueMeansFalse  False
        up2 (FakeE (Implication a b)) (pa, False) (pb, False) = genericUp2 a b pa pb falseMeansFalse True
        genericUp2 a b pa pb proof result = (foldl (S.|>) (pa S.>< pb) $
                                                substituteProof (mapAB (makeExpression a) (makeExpression b)) proof
                                            ,
                                            result)
        leafUp name = magic $ extract name valuesPair where
            magic (t, b) = (S.singleton $ makeExpression t, b)
        mapAB a b = DM.fromList [("A", a), ("B", b)]

simplifyProof exps = reverse $ removeRepetitions DS.empty (map decompose exps) [] where
    removeRepetitions s (e:es) res 
        | (show e) `DS.member` s = removeRepetitions s es res
        | otherwise              = removeRepetitions (DS.insert (show e) s) es (e:res)
    removeRepetitions _ [] res = res

excludePreposition :: File12 -> Either Value File12
excludePreposition f12f@(File12 (Hdr (excludedPrep:otherPreps) exp) _) = case generateTrivialProof (DS.fromList $ map show otherPreps, DS.singleton $ show excludedPrep) exp of
    (Left v)     -> Left v
    (Right f12s) -> Right $ File12 (Hdr otherPreps exp) (Proof (
        (getProofFromFile12 $ extractPreposition f12f) ++ 
        (getProofFromFile12 $ extractPreposition f12s) ++
        (substituteProof (DM.singleton (show excludedPrep) excludedPrep) excludedThird) ++
        (substituteProof (DM.fromList [("P", excludedPrep), ("A", exp)]) (map (decompose . parseExpression) [
            "(P->A)->(!P->A)->(P|!P)->A",
            "(!P->A)->(P|!P)->A",
            "(P|!P)->A",
            "A"]))))

collectPVars :: Expression -> DS.Set String
collectPVars exp = mapFMT (\_ s -> s) (\_ s1 s2 -> DS.union s1 s2) (\x -> DS.singleton x) (fakeWrap exp)

substituteProof :: DM.Map String Expression -> [Expression] -> [Expression]
substituteProof m proof = map (substitute m) proof

substitute :: DM.Map String Expression -> Expression -> Expression
substitute m exp = decompose $ unwrap $ mapFMT up1 up2 place $ fakeWrap exp where
    up1 (FakeT (An  _)) s = fakeWrap (An  (unwrap s))
    up1 (FakeT (Not _)) s = fakeWrap (Not (unwrap s))
    up1 (FakeC (Ac  _)) s = fakeWrap (Ac  (unwrap s))
    up1 (FakeD (Ad  _)) s = fakeWrap (Ad  (unwrap s))
    up1 (FakeE (Ae  _)) s = fakeWrap (Ae  (unwrap s))
    up2 (FakeC (And _ _)) s1 s2         = fakeWrap (And (unwrap s1) (unwrap s2))
    up2 (FakeD (Or  _ _)) s1 s2         = fakeWrap (Or  (unwrap s1) (unwrap s2))
    up2 (FakeE (Implication _ _)) s1 s2 = fakeWrap (Implication (unwrap s1) (unwrap s2))
    place str = fakeWrap $ An (m DM.! str)
