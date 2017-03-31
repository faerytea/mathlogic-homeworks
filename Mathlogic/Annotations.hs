module Mathlogic.Annotations where

import Mathlogic.Parser
import Mathlogic
import Data.List(intercalate)

type AnnotatedString = (Expression, String, Integer, Expression)

showAnnotatedString (e, s, c, _) = '(':(show c) ++ ')':(' ':(show e)) ++ ' ':('(':s) ++ ")"

annotateEng = annotate [
                        "Axiom No. ",
                        "Preposition No. ",
                        "M.P. ",
                        "Error"
                       ]   

annotate :: [String] -> File12 -> String -- [Strings] are strings like "Axiom no. ", "Preposition no. ", "M.P. ", "Doesn't prooved".
annotate strs (File12 header (Proof list)) = (show header) ++ ('\n':(intercalate "\n" (reverse (map showAnnotatedString (annotateItem ([], list) 1)))))
  where
    annotateItem :: ([AnnotatedString], [Expression]) -> Integer -> [AnnotatedString]
    annotateItem (all, []) _ = all
    annotateItem (done0, e0:exps) cntr = annotateItem ((magic header done0 e0 cntr):done0, exps) (cntr+1)
      where
        magic :: Header -> [AnnotatedString] -> Expression -> Integer -> AnnotatedString
        magic (Hdr prep exp) done e cnt
            | isAxiom (decompose e) /= 0                         = (e, (strs!!0) ++ show (isAxiom (decompose e)), cnt, decompose e)
            | checkPrep prep (decompose e) 1 /= 0                = (e, (strs!!1) ++ show (checkPrep prep (decompose e) 1), cnt, decompose e)
            | checkModusPonens done done (decompose e) /= (0, 0) = (e, (strs!!2) ++ show (fst (checkModusPonens done done (decompose e))) ++ ", " ++ show (snd (checkModusPonens done done (decompose e))), cnt, decompose e)
            | otherwise                                          = (e, (strs!!3), cnt, decompose e)

checkModusPonens :: [AnnotatedString] -> [AnnotatedString] -> Expression -> (Integer, Integer)
checkModusPonens [] _ _ = (0, 0)
checkModusPonens (d:done1) full expr = if ((fst (mayModusPonens full d expr)) /= 0) then (mayModusPonens full d expr) else (checkModusPonens done1 full expr)
  where
    mayModusPonens :: [AnnotatedString] -> AnnotatedString -> Expression -> (Integer, Integer)
    mayModusPonens full (_, _, num, (Implication from to1)) to2 = if to1 == to2 then (findModusPonens full (decompose (Ae from)), num) else (0,0) -- бага с циклом (Ae Ad Ac An)
      where
        findModusPonens :: [AnnotatedString] -> Expression -> Integer
        findModusPonens [] _ = 0
        findModusPonens ((_, _, n, a):rest) from = if a == from then n else findModusPonens rest from
    mayModusPonens _ _ _ = (0, 0)
