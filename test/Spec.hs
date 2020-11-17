import Test.Tasty
import Test.Tasty.HUnit

import Control.Monad (mapM_)
import qualified Language.Haskell.Exts.Syntax as Syntax (Decl)
import qualified Language.Haskell.Exts.SrcLoc as Ann    (SrcSpanInfo)
import qualified Language.Haskell.Exts.Parser as Parse  (ParseResult(..), parseDecl)

import Lib

main :: IO ()
main = defaultMain hunitTests

hunitTests = testGroup "HUnit tests"
  [ checkRecursiveTests
  , checkTailTests
  ]

checkRecursiveTests = testGroup "checkRecursive tests"
  [ onesIsRecursive
  , factorialExamplesAreRecursive
  , checkRecursiveIsAggressive
  , recursiveMap
  , mutualRecursion
  ]

checkTailTests = testGroup "checkTail tests"
  [ tailRecursiveMap
  , tailRecursiveFact
  , decListRecursive
  ]

parseDecl :: String -> Syntax.Decl Ann.SrcSpanInfo
parseDecl src = case Parse.parseDecl src of
  Parse.ParseOk d       -> d
  Parse.ParseFailed _ _ -> error "Couldn't parse example declaration"

onesIsRecursive :: TestTree
onesIsRecursive = testCase "ones" $
  assertBool "'ones' is not marked recursive" $ checkRecursive "ones = 1 : ones"

factorialExamplesAreRecursive :: TestTree
factorialExamplesAreRecursive = testCase "factorial examples" $ do
  mapM_ mkAssertion examples
  assertBool "factorial defined with 'product' is marked recursive" $
      not $ checkRecursive withProduct
  where
    mkAssertion (ix, src) = 
      assertBool ("example " ++ show ix ++ " is not marked recursive") $ checkRecursive src
    examples = zip [1..] [ex1, ex2, ex3, ex4, ex5]
    ex1 = "fact 0 = 1\nfact n = n * fact (n-1)\n"
    ex2 = "fact n | n == 0 = 1\nfact n = n * fact (n-1)\n"
    -- note the rest are recursive even though they don't all work
    ex3 = unlines [ "fact n = aux n 0"
                  , "  where aux 0 a = a"
                  , "        aux n a = aux (n-1) (a*n)" ]
    ex4 = unlines [ "fact n = aux n 0"
                  , "  where aux 0 a = 1"
                  , "        aux n a = n * aux (n-1) (a*n)" ]
    ex5 = unlines [ "fact n = aux n 0"
                  , "  where aux 0 a = 1"
                  , "        aux n a = n * fact (n-1)" ]
    withProduct = "fact n = product [1..n]"

checkRecursiveIsAggressive :: TestTree
checkRecursiveIsAggressive = testCase "unused binding" $ do
  assertBool "recursion check was fooled by a simple unused binding" $
    checkRecursive ex1
  assertBool "recursion check was fooled by complex unused bindings" $
    checkRecursive ex2
  where ex1 = unlines [ "fact n = product [1..n]"
                      , "  where _ = fact n" ]
        ex2 = unlines [ "fact n = product [1..n]"
                      , "  where go1 () = go2 ()"
                      , "        go2 () = go1 ()" ]

recursiveMap :: TestTree
recursiveMap = testCase "recursive map" $
  mapM_ mkAssertion examples
  where
    mkAssertion (ix, src) = 
      assertBool ("example " ++ show ix ++ " is not marked recursive") $
        checkRecursive src
    examples = zip [1..] [ex1, ex2, ex3]
    
    ex1 = "map _ [] = []\nmap f (x:xs) = let x' = f x in x' : map f xs"
    ex2 = "map _ [] = []\nmap f (x:xs) = let t = map f xs in f x : t"
    ex3 = unlines [ "map _ [] = []"
                  , "map f (x:xs) = let h = f x"
                  , "                   t = map f xs"
                  , "               in h:t" ]

mutualRecursion :: TestTree
mutualRecursion = testCase "mutually recursive local bindings" $
  assertBool "'even' is not marked recursive" $ checkRecursive exEven
  where
    exEven = unlines [ "even n = go1 n where"
                     , "  go1 0 = True"
                     , "  go1 n = go2 (n-1)"
                     , "  go2 0 = False"
                     , "  go2 n = go1 (n-1)" ]

checkTailSrc :: String -> Bool
checkTailSrc = check_tail . parseDecl

tailRecursiveMap :: TestTree
tailRecursiveMap = testCase "map" $
  assertBool "'map' is not marked tail recursive" $ checkTailSrc $
    unlines [ "map f xs = reverse $ go [] xs"
            , "  where go acc [] = acc"
            , "        go acc (x:xs) = go (f x : acc) xs" ]

tailRecursiveFact :: TestTree
tailRecursiveFact = testCase "fact" $ do
  assertBool "direct-recursive 'fact' marked tail recursive" $ 
    not . checkTailSrc $ "fact 0 = 1\nfact n = n * fact (n-1)"
  assertBool "tail-recursive 'fact' not marked tail recursive" $
    checkTailSrc $ unlines [ "fact = go 1 where"
                           , "  go a 0 = a"
                           , "  go a n = go (n*a) (n-1)" ]

-- This example is straight off practice exam 1 from FA2020
decListRecursive :: TestTree
decListRecursive = testCase "decList" $
  assertBool "'decList' not marked tail recursive" $
    checkTailSrc $
      unlines [ "decList = go []"
              , "  where go acc [] = reverse acc"
              , "        go acc (x:xs) = go (x-1 : acc) xs" ]