import Mathlogic.Predicates.Deduction
import Mathlogic.Predicates.Parser
import Mathlogic.Predicates.Checker(Wrong(..))

import System.Environment (getArgs)

resolveError :: Int -> Wrong -> String
resolveError n err = "Вывод некорректен начиная с формулы № " ++ (show n) ++ (case err of
                    (BoundedVariable v s e) -> ": терм " ++ s ++ " не свободен для подстановки в формулу " ++ (show e) ++ " вместо переменной " ++ v
                    (FreeVariable v e)      -> ": переменная " ++ v ++ " входит свободно в формулу " ++ (show e)
                    (BadUsageRule v e)      -> ": используется правило с квантором по переменной " ++ v ++ " входящей свободно в допущение " ++ show e
                    (BadUsageScheme v e)    -> ": используется схема аксиом с квантором по переменной " ++ v ++ " входящей свободно в допущение " ++ show e
                    _                       -> "") ++ "\n"

main = do
    inout <- getArgs
    if length inout /= 2
    then putStrLn "usage: homework4 <in> <out>"
    else do
        let ([inf,ouf]) = inout
        content <- readFile inf
        let parsed@(File4 (Hdr preps exp) proof) = parseFile4 content
        writeFile ouf $ if null preps
                        then case produce (File4 (Hdr [Predicate "!FAKE!" []] exp) proof) of
                            (Left (n, err)) -> resolveError n err
                            _               -> show parsed
                        else
                            let res = produce parsed
                            in case res of
                                (Left (n, err)) -> resolveError n err
                                (Right f4)      -> show f4 ++ "\n"
