module MathlogicCommon where

import Prelude(Show(..), String(..), (++), map, concat, Char(..), (==), drop, take, (-), (+), (&&), Eq(..), Bool(..), Int(..), Integral(..), (!!), (||), otherwise, fst, snd, error, ($), (.))
import Data.Either(Either(..), isRight)
import MathlogicParser
import MathlogicTokens(alexScanTokens)

type AxiomNo = Int
axioms :: [Expression]
axioms = [ax1, ax2, ax3, ax4, ax5, ax6, ax7, ax8, ax9, ax10]
  where
    ax1 = Implication (fScheme 'A') (Implication (fScheme 'B') (Ae (fScheme 'A')))
    ax2 = Implication (Ad (Ac (An (Implication (fScheme 'A') (Ae (fScheme 'B')))))) (Implication (Ad (Ac (An (Implication (fScheme 'A') (Implication (fScheme 'B') (Ae (fScheme 'C'))))))) (Implication (fScheme 'A') (Ae (fScheme 'C'))))
    ax3 = Implication (fScheme 'A') (Implication (fScheme 'B') (Ae (Ad (And (Ac (Scheme 'A')) (Scheme 'B')))))
    ax4 = Implication (Ad (And (Ac (Scheme 'A')) (Scheme 'B'))) (Ae (fScheme 'A'))
    ax5 = Implication (Ad (And (Ac (Scheme 'A')) (Scheme 'B'))) (Ae (fScheme 'B'))
    ax6 = Implication (fScheme 'A') (Ae (Or (fScheme 'A') (Ac (Scheme 'B'))))
    ax7 = Implication (fScheme 'B') (Ae (Or (fScheme 'A') (Ac (Scheme 'B'))))
    ax8 = Implication (Ad (Ac (An (Implication (fScheme 'A') (Ae (fScheme 'C')))))) (Implication (Ad (Ac (An (Implication (fScheme 'B') (Ae (fScheme 'C')))))) (Implication (Or (fScheme 'A') (Ac (Scheme 'B'))) (Ae (fScheme 'C'))))
    ax9 = Implication (Ad (Ac (An (Implication (fScheme 'A') (Ae (fScheme 'B')))))) (Implication (Ad (Ac (An (Implication (fScheme 'A') (Ae (Ad (Ac (Not (Scheme 'B'))))))))) (Ae (Ad (Ac (Not (Scheme 'A'))))))
    ax10= Implication (Ad (Ac (Not (Not (Scheme 'A'))))) (Ae (fScheme 'A'))
    fScheme :: Char -> Disjunction
    fScheme a = Ad (Ac (Scheme a))
    
extractRight :: Show a => Either a b -> b
extractRight (Right a) = a
extractRight (Left a) = error $ show $ a

isAxiom :: Expression -> AxiomNo
isAxiom exp = testNextAxiom exp 10
  where
    testNextAxiom :: Expression -> AxiomNo -> AxiomNo
    testNextAxiom exp 0 = 0
    testNextAxiom exp a = if (testAxiom exp a) /= [] then a else testNextAxiom exp (a-1)
    testAxiom :: Expression -> AxiomNo -> [(Char, Token)]
    testAxiom exp a = testExpression exp (axioms !! (a-1))
    testExpression (Ae          de)    (Ae          da)           = testDisjunction de da
    testExpression (Implication de ee) (Implication da ea)        = myMerge (testDisjunction de da) (testExpression ee ea)
    testExpression (               ee) (Ae (Ad (Ac (Scheme sa)))) = [(sa, An ee)]
    testExpression  _                   _                         = []
    testDisjunction (Ad ce)    (Ad ca)               = testConjunction ce ca
    testDisjunction (Or de ce) (Or da ca)            = myMerge (testDisjunction de da) (testConjunction ce ca)
    testDisjunction (   de)    (Ad (Ac (Scheme sa))) = [(sa, An (Ae de))]
    testDisjunction  _          _                    = []
    testConjunction (Ac  te)    (Ac  ta)         = testToken te ta
    testConjunction (And ce te) (And ca ta)      = myMerge (testConjunction ce ca) (testToken te ta)
    testConjunction (    ce)    (Ac (Scheme sa)) = [(sa, An (Ae (Ad ce)))]
    testConjunction  _           _               = []
    testToken (Not   te) (Not    ta) = testToken te ta
    testToken (An    ee) (An     ea) = testExpression ee ea
    testToken  te        (Scheme sa) = [(sa, te)]
    testToken  _          _          = []
    myMerge ll lr
        | ll == []       = []
        | lr == []       = []
        | ambigous ll lr = []
        | otherwise      = uniqueConcat ll lr
        where
            ambigous [] lr        = False
            ambigous (l:ll) lr    = (ambigousTest l lr) || (ambigous ll lr)
            ambigousTest l []     = False
            ambigousTest l (r:lr) = (((fst l) == (fst r)) && ((snd l) /= (snd r))) || (ambigousTest l lr)
            uniqueConcat = (++)

checkPrep :: Integral n => [Expression] -> Expression -> n -> n
checkPrep [] expr c = 0
checkPrep (p:prep) expr c
    | (decompose p) == expr = c
    | otherwise             = checkPrep prep expr (c+1)

parseFile12 = happilyParseFile12 . alexScanTokens
