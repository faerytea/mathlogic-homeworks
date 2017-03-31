module Mathlogic where

import Prelude(Show(..), String(..), (++), map, concat, Char(..), (==), drop, take, (-), (+), (&&), Eq(..), Bool(..), Int(..), Integral(..), (!!), (||), otherwise, fst, snd, error, ($), (.))
import Data.Either(Either(..), isRight)
import Data.Maybe(Maybe(..))
import Mathlogic.Parser
import Mathlogic.Tokens(alexScanTokens)
import Mathlogic.Axioms
    
extractRight :: Show a => Either a b -> b
extractRight (Right a) = a
extractRight (Left a) = error $ show a

isAxiom :: Expression -> AxiomNo
isAxiom exp = testNextAxiom exp 10
  where
    testNextAxiom :: Expression -> AxiomNo -> AxiomNo
    testNextAxiom exp 0 = 0
    testNextAxiom exp a = if (testAxiom exp a) /= [] then a else testNextAxiom exp (a-1)

getMathedAxiom :: Expression -> Maybe (AxiomNo, [(Char, Token)])
getMathedAxiom exp = getNextAxiom exp 10
  where
    getNextAxiom :: Expression -> AxiomNo -> Maybe (AxiomNo, [(Char, Token)])
    getNextAxiom exp 0 = Nothing
    getNextAxiom exp a = if (testAxiom exp a) /= [] then Just (a, testAxiom exp a) else getNextAxiom exp (a-1)

checkPrep :: Integral n => [Expression] -> Expression -> n -> n
checkPrep [] expr c = 0
checkPrep (p:prep) expr c
    | (decompose p) == expr = c
    | otherwise             = checkPrep prep expr (c+1)

parseFile12 = happilyParseFile12 . alexScanTokens

parseFile3 = parseExpression

parseExpression = happilyParseExpression . alexScanTokens
