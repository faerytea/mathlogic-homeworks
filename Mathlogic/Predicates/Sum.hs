module Mathlogic.Predicates.Sum where

import Mathlogic.Predicates.Parser
import Data.List(foldl')

genProof ai 0  = reverse $ genA0A (numToPeano ai) ++ map parseExpression ["A&B->B", "a+0=a"]
genProof ai bi = reverse (abab ++ a0a ++ abEQba) where
    ap = numToPeano ai
    bp = numToPeano bi
    Hatch bpd = bp
    (^+^) = Sum
    (^=^) a b = Predicate "=" [a, b]
    succPeanoFrom x = iterate Hatch (numToPeano x)
    a0a = genA0A ap            -- a''''+0=a''''
    upB bc cc = let im = Hatch $ ap ^+^ bc
                    bn = Hatch bc
                in  (finishProof im (ap ^+^ bn) (Hatch cc))
                 ++ (genRev (ap ^+^ bn) im)
                 ++ (genABAB (ap ^+^ bc) cc)
                 ++ (genABAB2 ap bc)
    abab = concatMap (\(bc,cc) -> upB bc cc) $ reverse $ take bi $ zip (succPeanoFrom 0) (succPeanoFrom ai)

substituteTerm :: String -> Term -> Expression -> Expression
substituteTerm var sub = st where
    checkSub orig = if orig == var then sub else Var orig
    st (Implication a b) = Implication (st a) (st b)
    st (Conjunction a b) = Conjunction (st a) (st b)
    st (Disjunction a b) = Disjunction (st a) (st b)
    st (Not a) = Not (st a)
    st (Predicate name ts) = Predicate name (map stt ts)
    st (Quantifier q v e) = if v == var then Quantifier q v e else Quantifier q v (st e)
    stt (Sum a b) = Sum (stt a) (stt b)
    stt (Production a b) = Production (stt a) (stt b)
    stt Zero = Zero
    stt (Hatch a) = Hatch (stt a)
    stt (Function name ts) = Function name (map stt ts)
    stt (Var v) = (checkSub v)

numToPeano x = foldl' (\a f -> f a) Zero $ replicate x Hatch

peanoToNum Zero = 0
peanoToNum (Hatch a) = 1 + peanoToNum a

abEQba = reverse $ map parseExpression [ "a=b->a=c->b=c"
                                       , "A&B->B" -- just short axiom (can be freely replaced with any other)
                                       , "(a=b->a=c->b=c)->((A&B->B)->(a=b->a=c->b=c))"
                                       , "(A&B->B)->(a=b->a=c->b=c)"
                                       , "(A&B->B)->@c(a=b->a=c->b=c)"
                                       , "@c(a=b->a=c->b=c)"
                                       , "@c(a=b->a=c->b=c)->(a=b->a=a->b=a)"
                                       , "a=b->a=a->b=a"
                                       , "a=a->a=b->a=a"
                                       , "(a=b->a=a->b=a)->a=a->a=b->a=a->b=a"
                                       , "a=a->a=b->a=a->b=a"
                                       , "(a=b->a=a)->(a=b->a=a->b=a)->a=b->b=a"
                                       , "((a=b->a=a)->(a=b->a=a->b=a)->a=b->b=a)->a=a->(a=b->a=a)->(a=b->a=a->b=a)->a=b->b=a"
                                       , "a=a->(a=b->a=a)->(a=b->a=a->b=a)->a=b->b=a"
                                       , "(a=a->a=b->a=a)->(a=a->(a=b->a=a)->(a=b->a=a->b=a)->a=b->b=a)->a=a->(a=b->a=a->b=a)->a=b->b=a"
                                       , "(a=a->(a=b->a=a)->(a=b->a=a->b=a)->a=b->b=a)->a=a->(a=b->a=a->b=a)->a=b->b=a"
                                       , "a=a->(a=b->a=a->b=a)->(a=b->b=a)"
                                       , "(a=a->a=b->a=a->b=a)->(a=a->(a=b->a=a->b=a)->a=b->b=a)->a=a->a=b->b=a"
                                       , "(a=a->(a=b->a=a->b=a)->a=b->b=a)->a=a->a=b->b=a"
                                       , "a=a->a=b->b=a" -- there should be 2 more lines, see lines 4-5
                                       , "(A&B->B)->@b@c(a=b->a=c->b=c)"
                                       , "(A&B->B)->@a@b@c(a=b->a=c->b=c)"
                                       , "@a@b@c(a=b->a=c->b=c)"
                                       , "@a@b@c(a=b->a=c->b=c)->@b@c(a+0=b->a+0=c->b=c)"
                                       , "@b@c(a+0=b->a+0=c->b=c)"
                                       , "@b@c(a+0=b->a+0=c->b=c)->@c(a+0=a->a+0=c->a=c)"
                                       , "@c(a+0=a->a+0=c->a=c)"
                                       , "@c(a+0=a->a+0=c->a=c)->(a+0=a->a+0=a->a=a)"
                                       , "a+0=a"
                                       , "(a+0=a->a+0=a->a=a)"
                                       , "a+0=a->a=a"
                                       , "a=a"
                                       , "a=b->b=a" ]

genA0A a = Predicate "=" [Sum a Zero, a]
         : Implication
             (Quantifier All "a" (Predicate "=" [Sum (Var "a") Zero, (Var "a")]))
             (Predicate "=" [Sum a Zero, a])
         : baseA0A

baseA0A = reverse $ map parseExpression [ "(a+0=a)->(A&B->B)->(a+0=a)"
                                        , "(A&B->B)->(a+0=a)"
                                        , "(A&B->B)->@a(a+0=a)"
                                        , "@a(a+0=a)" ]

genABAB a b = (reverse $ map (substituteTerm "a" a
                            . substituteTerm "b" b
                            . parseExpression) [ "@a@b((a=b)->(a'=b'))->@b((a=b)->(a'=b'))"
                                               , "@b((a=b)->(a'=b'))"
                                               , "@b((a=b)->(a'=b'))->((a=b)->(a'=b'))"
                                               , "(a=b)->(a'=b')"
                                               , "a'=b'" ]) -- TODO
           ++ baseABAB

baseABAB = reverse $ map parseExpression [ "(a=b)->(a'=b')"
                                         , "((a=b)->(a'=b'))->(A&B->B)->(a=b)->(a'=b')"
                                         , "(A&B->B)->(a=b)->(a'=b')"
                                         , "(A&B->B)->@b((a=b)->(a'=b'))"
                                         , "(A&B->B)->@a@b((a=b)->(a'=b'))"
                                         , "@a@b((a=b)->(a'=b'))"]

genABAB2 a b = (reverse $ map (substituteTerm "a" a
                             . substituteTerm "b" b
                             . parseExpression) [ "@a@b(a+b'=(a+b)')->@b(a+b'=(a+b)')"
                                                , "@b(a+b'=(a+b)')"
                                                , "@b(a+b'=(a+b)')->(a+b'=(a+b)')"
                                                , "(a+b'=(a+b)')" ])
            ++ baseABAB2

baseABAB2 = reverse $ map parseExpression [ "(a+b'=(a+b)')"
                                          , "(a+b'=(a+b)')->(A&B->B)->(a+b'=(a+b)')"
                                          , "(A&B->B)->(a+b'=(a+b)')"
                                          , "(A&B->B)->@b(a+b'=(a+b)')"
                                          , "(A&B->B)->@a@b(a+b'=(a+b)')"
                                          , "@a@b(a+b'=(a+b)')"]

genRev a b = (reverse $ map (substituteTerm "a" a
                           . substituteTerm "b" b
                           . parseExpression) [ "@a@b((a=b)->(b=a))->@b((a=b)->(b=a))"
                                               , "@b((a=b)->(b=a))"
                                               , "@b((a=b)->(b=a))->(a=b)->(b=a)"
                                               , "(a=b)->(b=a)"
                                               , "(b=a)"])
      ++ baseRev

baseRev = reverse $ map parseExpression [ "((a=b)->(b=a))->(A&B->B)->(a=b)->(b=a)"
                                        , "(A&B->B)->(a=b)->(b=a)"
                                        , "(A&B->B)->@b((a=b)->(b=a))"
                                        , "(A&B->B)->@a@b((a=b)->(b=a))"
                                        , "@a@b((a=b)->(b=a))"]

finishProof a b c = reverse $ map (substituteTerm "a" a
                                 . substituteTerm "b" b
                                 . substituteTerm "c" c
                                 . parseExpression) [ "@a@b@c((a=b)->(a=c)->(b=c))->@b@c((a=b)->(a=c)->(b=c))"
                                                    , "@b@c((a=b)->(a=c)->(b=c))" -- see a=a proof
                                                    , "@b@c((a=b)->(a=c)->(b=c))->@c((a=b)->(a=c)->(b=c))"
                                                    , "@c((a=b)->(a=c)->(b=c))"
                                                    , "@c((a=b)->(a=c)->(b=c))->((a=b)->(a=c)->(b=c))"
                                                    , "(a=b)->(a=c)->(b=c)"
                                                    , "(a=c)->(b=c)"
                                                    , "b=c"]
