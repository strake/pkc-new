import Control.Category.Unicode
import Distribution.Simple
import Distribution.Simple.PreProcess
import System.Process

main = defaultMainWithHooks $
       simpleUserHooks {
           hookedPreProcessors =
             ("g",
              \ _ _ -> PreProcessor True ∘ mkSimplePreProcessor $ \ inPath outPath verb ->
              readFile inPath >>= readProcess "frown" ["-Occompact", "-l", "frownScan"] >>= writeFile outPath):hookedPreProcessors simpleUserHooks
       }
