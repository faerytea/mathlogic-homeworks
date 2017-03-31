import Mathlogic
import Mathlogic.Annotations
import Prelude(Show(..), String(..), Integer(..), head, tail, lines, (++), reverse, map, (!!), fst, snd, (+), (==), (/=), otherwise, return, ($))
import System.Environment(getArgs)
import Data.Text(pack, unpack)
import Data.Text.IO(readFile, writeFile, appendFile)

main = do
    args <- getArgs
    str <- readFile (head args)
    ans <- readFile ("strings")
    writeFile (head $ tail $ args) (pack $ (annotate (lines $ unpack ans) $ parseFile12 (unpack str)))
    appendFile (head $ tail $ args) (pack "\n")
    return ()
