module Mathlogic.Predicates.Axioms where

import Mathlogic.Predicates.Parser
import Mathlogic.Predicates.Tokens
import qualified Data.Map.Strict as DM
import qualified Data.Set as DS
import Data.Foldable(foldl', find)
import Data.Maybe(fromJust)

type AxiomNo = Int
type Axiom = Expression

data AxiomError = NotAnAxiom | Bounded String String Expression deriving (Eq, Show)

getMathedAxiom :: Expression -> Either AxiomError (AxiomNo, DM.Map String Expression)
getMathedAxiom e
    | classicMatch /= Nothing        = Right $ fromJust classicMatch
    | anyAxiom /= Left NotAnAxiom    = prepareLastAxiom anyAxiom 11
    | existsAxiom /= Left NotAnAxiom = prepareLastAxiom existsAxiom 12
    | otherwise                      = Left NotAnAxiom where
        classicMatch = find (\(_, m) -> nonEmpty m) $ zip [1..10] $ map (\a -> findSubstitution a e) classicAxioms
        anyAxiom = test11Axiom e
        existsAxiom = test12Axiom e
        nonEmpty = not . DM.null
        prepareLastAxiom a n = case a of
            (Left bounded)       -> Left bounded
            (Right substitution) -> Right (n, substitution)

classicAxioms :: [Axiom]
classicAxioms = map (happilyParseExpression . alexScanTokens) $ [
    "~A->~B->~A",
    "(~A->~B)->(~A->~B->~C)->~A->~C",
    "~A->~B->~A&~B",
    "~A&~B->~A",
    "~A&~B->~B",
    "~A->~A|~B",
    "~B->~A|~B",
    "(~A->~C)->(~B->~C)->~A|~B->~C",
    "(~A->~B)->(~A->!~B)->!~A",
    "!!~A->~A"]

testClassicAxiom :: Expression -> AxiomNo -> DM.Map String Expression
testClassicAxiom exp an = findSubstitution (classicAxioms !! (an - 1)) exp
findSubstitution :: Axiom -> Expression -> DM.Map String Expression
findSubstitution (Implication aa ab) (Implication ea eb) = merge (findSubstitution aa ea) (findSubstitution ab eb)
findSubstitution (Conjunction aa ab) (Conjunction ea eb) = merge (findSubstitution aa ea) (findSubstitution ab eb)
findSubstitution (Disjunction aa ab) (Disjunction ea eb) = merge (findSubstitution aa ea) (findSubstitution ab eb)
findSubstitution (Not a) (Not e) = findSubstitution a e
findSubstitution (Scheme a) e = DM.singleton a e
findSubstitution a e = DM.empty
merge m1 m2 
    | (DM.null m1) || (DM.null m2) = DM.empty
    | otherwise = if DM.foldr (&&) True $ DM.intersectionWith (\a b -> a == b) m1 m2 then DM.union m1 m2
                                                                                     else DM.empty

freeForSubstitution --see str 61. use intersection

test11Axiom :: Expression -> Either AxiomError (DM.Map String Expression)
test11Axiom (Implication q@(Quantifier All var psi) spsi) 
    | (substitution /= "!") 
        && (isVariableFree substitution spsi) = Right $ DM.fromList [("A", q), ("A[" ++ var ++ ":=" ++ substitution ++ "]", spsi)]
    | (substitution /= "!")                   = Left $ Bounded var substitution psi
    | otherwise                               = Left NotAnAxiom where
        substitution = findSubstitutionVariable var psi spsi
test11Axiom _ = Left NotAnAxiom

test12Axiom :: Expression -> Either AxiomError (DM.Map String Expression)
test12Axiom (Implication spsi q@(Quantifier Ex var psi))
    | (substitution /= "!") 
        && (isVariableFree substitution spsi) = Right $ DM.fromList [("A", q), ("A[" ++ var ++ ":=" ++ substitution ++ "]", spsi)]
    | (substitution /= "!")                   = Left $ Bounded var substitution psi
    | otherwise                               = Left NotAnAxiom where
        substitution = findSubstitutionVariable var psi spsi
test12Axiom _ = Left NotAnAxiom

findSubstitutionVariable var (Implication aa ab) (Implication ba bb) = check (findSubstitutionVariable var aa ba) (findSubstitutionVariable var ab bb)
findSubstitutionVariable var (Conjunction aa ab) (Conjunction ba bb) = check (findSubstitutionVariable var aa ba) (findSubstitutionVariable var ab bb)
findSubstitutionVariable var (Disjunction aa ab) (Disjunction ba bb) = check (findSubstitutionVariable var aa ba) (findSubstitutionVariable var ab bb)
findSubstitutionVariable var (Not a) (Not b) = findSubstitutionVariable var a b
findSubstitutionVariable var (Predicate an ats) (Predicate bn bts) = if an == bn then checkTF var ats bts else "!"
findSubstitutionVariable var (Quantifier aq av ae) (Quantifier bq bv be)
    | (aq /= bq) || (av /= bv) = "!"
    | otherwise                = findSubstitutionVariable var ae be
findSubstitutionVariable var a b = "!"
check a b
    | (a == "!") || (b == "!") = "!"
    | a == ""                  = b
    | b == ""                  = a
    | a /= b                   = "!"
    | otherwise                = a
checkTF var ats bts = if length ats == length bts then foldl' check "" $ map (uncurry (findSubstitutionVariableT var)) $ zip ats bts else "!"
findSubstitutionVariableT var (Sum aa ab) (Sum ba bb) = check (findSubstitutionVariableT var aa ba) (findSubstitutionVariableT var ab bb)
findSubstitutionVariableT var (Production aa ab) (Production ba bb) = check (findSubstitutionVariableT var aa ba) (findSubstitutionVariableT var ab bb)
findSubstitutionVariableT var (Hatch a) (Hatch b) = findSubstitutionVariableT var a b
findSubstitutionVariableT var (Zero) (Zero) = ""
findSubstitutionVariableT var (Function an ats) (Function bn bts) = if an == bn then checkTF var ats bts else "!"
findSubstitutionVariableT var (Var av) (Var bv)
    | av == var = bv
    | av == bv  = ""
    | otherwise = "!"
findSubstitutionVariableT _ _ _ = "!"
