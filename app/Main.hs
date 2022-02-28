module Main where

import System.Environment (getArgs)
import Lib

main :: IO ()
main = do
  args <- getArgs
  result <- case args of
    []      -> error "CodeProperty: no file"
    xs -> mapM (\x -> print x >> graphFromFile x "fact") xs
    -- (fpath : names) -> testModuleFromFile fpath names
  print result
