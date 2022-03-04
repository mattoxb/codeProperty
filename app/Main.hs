module Main where

import System.Environment (getArgs)
import Lib

main :: IO ()
main = do
  args <- getArgs
  result <- case args of
    []      -> error "CodeProperty: no file"
    [name, file] -> testModuleFromFile file name
    _ -> error "Too many args"
    -- (fpath : names) -> testModuleFromFile fpath names
  print result
