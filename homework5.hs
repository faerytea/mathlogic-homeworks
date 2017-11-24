import Mathlogic.Predicates.Sum
import Mathlogic.Predicates.Parser(File4(..), Header(..), Proof, Expression(..), Term(..))

import System.Environment (getArgs)

main = do
    args <- getArgs
    if length args < 2 || length args > 3
    then putStrLn "Usage: homework5 <a> <b> [output]"
    else do
        let [a, b] = map read $ take 2 args
            proof = genProof a b
            f4 = File4 (Hdr [] (Predicate "=" [Sum (numToPeano a) (numToPeano b), numToPeano (a+b)])) proof
            in (if length args == 3
                then writeFile (args !! 2)
                else putStrLn) (show f4)
