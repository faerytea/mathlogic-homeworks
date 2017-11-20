module Mathlogic.Predicates.Axioms where

import Mathlogic.Predicates.Parser
import Mathlogic.Predicates.Tokens
import qualified Data.Map.Strict as DM
import qualified Data.Set as DS
import Data.Foldable(foldl', find)
import Data.Maybe(fromJust)
import Debug.Trace(trace)

type AxiomNo = Int
type Axiom = Expression

data AxiomError = NotAnAxiom | Bounded String String Expression deriving (Eq, Show)

getMathedAxiom :: Expression -> Either AxiomError (AxiomNo, DM.Map String Expression)
getMathedAxiom e
    | peanoMatch > 0                 = Right (peanoMatch + 12, DM.empty)
    | classicMatch /= Nothing        = Right $ fromJust classicMatch
    | inductionMatch /= Nothing      = Right (21, DM.singleton "A" $ fromJust inductionMatch)
    | anyAxiom /= Left NotAnAxiom    = prepareLastAxiom anyAxiom 11
    | existsAxiom /= Left NotAnAxiom = prepareLastAxiom existsAxiom 12
    | otherwise                      = Left NotAnAxiom where
        classicMatch = find (\(_, m) -> nonEmpty m) $ zip [1..10] $ map (\a -> findSubstitution a e) classicAxioms
        peanoMatch = foldl' (\p (n, a) -> if p > 0 then p else if a == e then n else 0) 0 $ zip [1..] peanoAxioms
        inductionMatch = testInduction e
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

peanoAxioms = map (happilyParseExpression . alexScanTokens) $ [
    "a=b->a'=b'",
    "a=b->a=c->b=c",
    "a'=b'->a=b",
    "!a'=0",
    "a+b'=(a+b)'",
    "a+0=a",
    "a*0=0",
    "a*b'=a*b+a"]

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

testInduction :: Expression -> Maybe Expression
testInduction (Implication (Conjunction psiz (Quantifier All var (Implication psif psin))) psi) =
    if psi == psif && checkInduction psiz psi psin then Just psi
                                                   else Nothing where
        checkInduction (Implication az bz) (Implication a b) (Implication an bn) = checkInduction az a an && checkInduction bz b bn
        checkInduction (Conjunction az bz) (Conjunction a b) (Conjunction an bn) = checkInduction az a an && checkInduction bz b bn
        checkInduction (Disjunction az bz) (Disjunction a b) (Disjunction an bn) = checkInduction az a an && checkInduction bz b bn
        checkInduction (Not az) (Not a) (Not an) = checkInduction az a an
        checkInduction (Quantifier qz nz ez) (Quantifier q n e) (Quantifier qn nn en) =
            qz == q && q == qn && nz == n && n == nn && checkInduction ez e en
        checkInduction (Predicate nz lz) (Predicate n l) (Predicate nn ln) =
            nz == n && n == nn && (all (\(z, c, x) -> checkIndT z c x) $ zip3 lz l ln)
        checkInduction _ _ _ = False
        checkIndT (Sum az bz) (Sum a b) (Sum an bn) = checkIndT az a an && checkIndT bz b bn
        checkIndT (Production az bz) (Production a b) (Production an bn) = checkIndT az a an && checkIndT bz b bn
        checkIndT (Function fz az) (Function f a) (Function fn an) =
            fz == f && f == fn && (all (\(z, c, x) -> checkIndT z c x) $ zip3 az a an)
        checkIndT (Hatch tz) (Hatch t) (Hatch tn) = checkIndT tz t tn
        checkIndT (Zero) (Zero) (Zero) = True
        -- memes starts here
        checkIndT (Var vz) (Var v) (Var vn) = vz == v && v == vn && v /= var
        checkIndT (Zero) (Var v) (Hatch (Var vn)) = v == vn && v == var
        checkIndT _ _ _ = False
testInduction _ = Nothing

data VarSub = SubToTerm Term | SubToAny | NoSub deriving (Eq, Show)

freeForSubstitution :: Term -> String -> Expression -> Bool
freeForSubstitution subst orig expr = safe expr where
    vars :: DS.Set String
    vars = walkTerm DS.singleton DS.empty (\_ -> DS.unions) subst
    chk s = DS.member s vars
    safe (Implication a b) = safe a && safe b
    safe (Conjunction a b) = safe a && safe b
    safe (Disjunction a b) = safe a && safe b
    safe (Not a) = safe a
    safe (Predicate _ terms) = True
    safe (Quantifier _ var exp)
        | var == orig  = trace ("duble quantified " ++ var ++ " in " ++ show expr) (safe exp)
        | chk var      = danger exp
        | otherwise    = safe exp
    danger (Implication a b) = danger a && danger b
    danger (Conjunction a b) = danger a && danger b
    danger (Disjunction a b) = danger a && danger b
    danger (Not a) = danger a
    danger (Predicate _ terms) = all dangerT terms
    danger (Quantifier _ var exp)
        | var == orig ||
          chk var      = trace ("duble quantified " ++ var ++ " in " ++ show expr) (danger exp)
        | otherwise    = danger exp
    dangerT (Sum a b) = dangerT a && dangerT b
    dangerT (Production a b) = dangerT a && dangerT b
    dangerT (Hatch a) = dangerT a
    dangerT (Zero) = True
    dangerT (Function _ terms) = all dangerT terms
    dangerT (Var var) = var /= orig

test11Axiom :: Expression -> Either AxiomError (DM.Map String Expression)
test11Axiom (Implication q@(Quantifier All var psi) spsi)
    | (substitution == NoSub)    = Left NotAnAxiom
    | (substitution == SubToAny) = Right $ DM.fromList [("A", q), ("A[" ++ var ++ ":=" ++ val ++ "]", spsi)]
    | (freeForSubstitution subTerm var psi)
                                 = Right $ DM.fromList [("A", q), ("A[" ++ var ++ ":=" ++ val ++ "]", spsi)]
    | otherwise                  = Left $ Bounded var val psi where
        substitution = findSubstitutionVariable var psi spsi
        (SubToTerm subTerm) = substitution
        val = case substitution of
                  (SubToTerm term) -> show term
                  (SubToAny)       -> ""
test11Axiom _ = Left NotAnAxiom

test12Axiom :: Expression -> Either AxiomError (DM.Map String Expression)
test12Axiom (Implication spsi q@(Quantifier Ex var psi))
    | (substitution == NoSub)    = Left NotAnAxiom
    | (substitution == SubToAny) = Right $ DM.fromList [("A", q), ("A[" ++ var ++ ":=" ++ val ++ "]", spsi)]
    | (freeForSubstitution subTerm var psi)
                                 = Right $ DM.fromList [("A", q), ("A[" ++ var ++ ":=" ++ val ++ "]", spsi)]
    | otherwise                  = Left $ Bounded var val psi where
        substitution = findSubstitutionVariable var psi spsi
        (SubToTerm subTerm) = substitution
        val = case substitution of
                  (SubToTerm term) -> show term
                  (SubToAny)       -> ""
test12Axiom _ = Left NotAnAxiom

findSubstitutionVariable var (Implication aa ab) (Implication ba bb) = check (findSubstitutionVariable var aa ba) (findSubstitutionVariable var ab bb)
findSubstitutionVariable var (Conjunction aa ab) (Conjunction ba bb) = check (findSubstitutionVariable var aa ba) (findSubstitutionVariable var ab bb)
findSubstitutionVariable var (Disjunction aa ab) (Disjunction ba bb) = check (findSubstitutionVariable var aa ba) (findSubstitutionVariable var ab bb)
findSubstitutionVariable var (Not a) (Not b) = findSubstitutionVariable var a b
findSubstitutionVariable var (Predicate an ats) (Predicate bn bts) = if an == bn then checkTF var ats bts else NoSub
findSubstitutionVariable var (Quantifier aq av ae) (Quantifier bq bv be)
    | (aq /= bq) || (av /= bv) = NoSub
    | otherwise                = findSubstitutionVariable var ae be
findSubstitutionVariable var a b = NoSub
check a b
    | (a == NoSub) || (b == NoSub) = NoSub
    | a == SubToAny                = b
    | b == SubToAny                = a
    | a /= b                       = NoSub
    | otherwise                    = a
checkTF var ats bts = if length ats == length bts then foldl' check SubToAny $ map (uncurry (findSubstitutionVariableT var)) $ zip ats bts else NoSub
findSubstitutionVariableT var (Sum aa ab) (Sum ba bb) = check (findSubstitutionVariableT var aa ba) (findSubstitutionVariableT var ab bb)
findSubstitutionVariableT var (Production aa ab) (Production ba bb) = check (findSubstitutionVariableT var aa ba) (findSubstitutionVariableT var ab bb)
findSubstitutionVariableT var (Hatch a) (Hatch b) = findSubstitutionVariableT var a b
findSubstitutionVariableT var (Zero) (Zero) = SubToAny
findSubstitutionVariableT var (Function an ats) (Function bn bts) = if an == bn then checkTF var ats bts else NoSub
findSubstitutionVariableT var a@(Var v) term
    | v == var  = SubToTerm term
    | a == term = SubToAny
    | otherwise = NoSub
findSubstitutionVariableT _ _ _ = NoSub
