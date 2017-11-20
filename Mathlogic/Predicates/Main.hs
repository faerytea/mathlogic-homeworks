import Mathlogic.Predicates.Checker
import Mathlogic.Predicates.Parser

import System.Environment (getArgs)

main = do
    (file:_) <- getArgs
    content <- readFile file
    let res = checkProof $ parseFile4 content
    putStrLn (show res)
