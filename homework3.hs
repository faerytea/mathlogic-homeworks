import Mathlogic.Proof
import Mathlogic
import Prelude hiding (readFile, writeFile, appendFile)
import System.Environment(getArgs)
import Data.Text(pack, unpack)
import Data.Text.IO(readFile, writeFile, appendFile)
import Data.Set(member)
import Data.Foldable(toList)

main = do
    args <- getArgs
    if ((length args) /= 2) then putStrLn "Usage: ./homework3 input.in output.out"
                            else action args
    
action args = do
    str <- readFile (head args)
    let answer = case generateProof $ parseFile3 (unpack str) of 
                        Left (t,f) -> "Высказывание ложно при " ++ (concat $ map (\x -> x ++ "=" ++ (if x `member` t then "И" else "Л")) ((toList t) ++ (toList f)))
                        Right f12  -> show f12
    writeFile (head $ tail $ args) (pack answer)
    appendFile (head $ tail $ args) (pack "\n")
    return ()
