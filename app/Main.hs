module Main where

import Lib (testModuleFromFile)
import System.Environment (getArgs)

main :: IO ()
main = do
  args <- getArgs
  result <- case args of
    []      -> error "CodeProperty: no file"
    [fpath] -> pure True
    (fpath : names) -> testModuleFromFile fpath names
  print result
