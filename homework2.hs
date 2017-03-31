import Mathlogic
import Mathlogic.Deduction
import Prelude hiding (readFile, writeFile, appendFile)
import System.Environment(getArgs)
import Data.Text(pack, unpack)
import Data.Text.IO(readFile, writeFile, appendFile)

main = do
    args <- getArgs
    str <- readFile (head args)
    writeFile (head $ tail $ args) (pack $ (show $ extractPreposition $ parseFile12 (unpack str)))
    appendFile (head $ tail $ args) (pack "\n")
    return ()
