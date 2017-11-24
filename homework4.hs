import Mathlogic.Predicates.Deduction
import Mathlogic.Predicates.Parser
import Mathlogic.Predicates.Checker(Wrong(..))

import System.Environment (getArgs)

main = do
    inout <- getArgs
    if length inout /= 2
    then putStrLn "usage: homework4 <in> <out>"
    else do
        let ([inf,ouf]) = inout
        content <- readFile inf
        let parsed@(File4 (Hdr preps exp) proof) = parseFile4 content
        if null preps
        then writeFile ouf (show parsed)
        else
            let res = produce parsed
            in writeFile ouf $ case res of
                (Left (n, error)) -> "Вывод некорректен начиная с формулы № " ++ (show n) ++ case error of
                    (BoundedVariable v s e) -> ": терм " ++ s ++ " не свободен для подстановки в формулу " ++ (show e) ++ " вместо переменной " ++ v
                    (FreeVariable v e)      -> ": переменная " ++ v ++ " входит свободно в формулу " ++ (show e)
                    (BadUsageRule v e)      -> ": используется правило с квантором по переменной " ++ v ++ " входящей свободно в допущение " ++ show e
                    (BadUsageScheme v e)    -> ": используется схема аксиом с квантором по переменной " ++ v ++ " входящей свободно в допущение " ++ show e
                    _                       -> ""
                (Right f4)        -> show f4 ++ "\n"
