module Lib where

import Data.Functor (void)
import System.FilePath (takeFileName)

import qualified Language.Haskell.Exts as HS
import ContainsListComp (containsListComp)
import TailRecursion (tailRecursiveInModule)
import CPS (CpsModule, Name, renameModule, cpsTransformModule)
import CallGraph

-- | Process a parsed Haskell module to make it suitable for use in the
-- tail recursion checker.
processModule :: HS.Module () -> Maybe CpsModule
processModule mod
  | containsListComp mod = Nothing
  | otherwise = Just $ renameModule $ cpsTransformModule mod

data ModuleSource = ModSrc FilePath String

parseModuleSource :: ModuleSource -> HS.Module ()
parseModuleSource (ModSrc name src) = void $ HS.fromParseResult parseResult
  where
    parseMode = HS.defaultParseMode { HS.parseFilename = name }
    parseResult = HS.parseModuleWithMode parseMode src

getModuleSource :: FilePath -> IO ModuleSource
getModuleSource fpath = do
  fileContents <- readFile fpath
  return $ ModSrc (takeFileName fpath) fileContents

testModule :: HS.Module () -> [Name] -> Bool
testModule mod names = case processModule mod of
  Nothing -> False
  Just cpsMod -> tailRecursiveInModule cpsMod names

testModuleFromFile :: FilePath -> [Name] -> IO Bool
testModuleFromFile fpath names = do
  modsrc <- getModuleSource fpath
  return $ testModule (parseModuleSource modsrc) names

graphFromFile :: FilePath -> IO ()
graphFromFile fpath = do
  modsrc <- getModuleSource fpath
  let mod = parseModuleSource modsrc
  case processModule mod of
    Nothing -> return ()
    Just cpsMod -> do
      print cpsMod
      let (graph, ctx) = buildGraph emptyContext cpsMod
      print graph