module Lib where

import Data.Functor (void)
import System.FilePath (takeFileName)

import qualified Language.Haskell.Exts as HS
import ContainsListComp (containsListComp)
import TailRecursion (Truth (Fails))
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

testModuleFromFile :: FilePath -> Name -> IO Truth
testModuleFromFile fpath name = do
  modsrc@(ModSrc _ contents) <- getModuleSource fpath
  -- putStrLn contents
  let mod = parseModuleSource modsrc
  case processModule mod of
    Nothing ->
      return Fails
    Just cpsMod -> do
      let (graph, _) = buildGraph emptyContext cpsMod
      -- print cpsMod
      -- print graph
      return $ isTailRecursive name graph