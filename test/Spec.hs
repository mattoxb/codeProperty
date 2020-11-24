import Test.Tasty
import Test.Tasty.HUnit

import Control.Monad (mapM_)
import qualified Language.Haskell.Exts.Syntax as Syntax (Decl)
import qualified Language.Haskell.Exts.SrcLoc as Ann    (SrcSpanInfo)
import qualified Language.Haskell.Exts.Parser as Parse

import Lib hiding (cpsExp)
import CPS
import TailRecursion

-- I'd like to write a property test like
-- prop_renameLeavesFvs exp = sort (alLRawBinders (renameExp exp)) == freeVars exp
-- but I really don't know how to make a good Arbitrary instance for CpsExp.

main :: IO ()
main = defaultMain hunitTests

hunitTests = testGroup "HUnit tests"
  [ --checkRecursiveTests
  --, checkTailTests
  {-,-} refersToTests
  , onlyTailCallsNoLetTests
  , cpsTailRecursiveTests
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
  assertBool "recursion check didn't see simple unused binding" $
    checkRecursive ex1
  assertBool "recursion check didn't see complex unused bindings" $
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

-------------------------------------------------------------------------------
-- TailRecursion.hs
-------------------------------------------------------------------------------

type Source = String
type Desc   = String

processExp :: Source -> CpsExp
processExp src = case Parse.parseExp src of
  Parse.ParseOk exp ->
    let cpsE = runCPSM $ do kvar <- freshKVar
                            cpsExp exp (VarCont kvar)
        cpsRN = runRn $ renameExp cpsE
    in cpsRN
  Parse.ParseFailed{} -> error "processExp: couldn't parse exp source"

processDecl src = case Parse.parseDecl src of
  Parse.ParseOk d -> case runCPSM $ cpsBinding d of
    Just bind -> runRn $ renameBinding bind
    Nothing   -> error "processDecl: decl is not a binding"
  Parse.ParseFailed{} -> error "processDecl: couldn't parse decl source"

testFromSource :: (Eq result, Show result)
               => (CpsExp -> [Binder] -> result)
               -> (Desc, [Name], Source, result) -> TestTree
testFromSource f (desc, arg, src, expected) = testCase desc $
  expected @=? f (processExp src) (map BindRaw arg)

onlyTailCallsNoLetTests :: TestTree
onlyTailCallsNoLetTests = testGroup "onlyTailCalls (no let)" $ map check
  [ ("simple example", ["rev"], "rev (x:acc) xs", Holds)
  , ("tail call inside lambda 1", ["rev"], "(\\() -> rev) (x:acc) xs", Fails)
  , ("tail call inside lambda 2", ["foo"], "\\x -> foo ()", Holds)
  , ("reverse", ["rev"], revBody, Holds)
  , ("vacuous 1", [], "(foo x, bar y, [1, 2, z])", Vacuous)
  , ("vacuous 2", ["doesNotAppear"], "tail (x+y)", Vacuous)
  , ("non-tail", ["acc"], revBody, Fails)
  , ("one good and one bad 1", ["acc", "rev"], revBody, Fails)
  , ("one good and one bad 2", ["rev", "acc"], revBody, Fails)
  , ("dead simple", ["s"], "s", Holds)
  , ("dead simple application", ["s"], "s 0", Holds)
  , ("dead simple argument", ["s"], "() s", Fails)
  , ("omega", ["omega"], "omega omega", Fails)
  , ("dead simple paren", ["s"], "(s)", Holds)
  , ("dead simple tuple", ["s"], "(s, 0)", Fails)
  ]

  where revBody = "case lst of [] -> acc; (x:xs) -> rev (x:acc) xs"

        -- onlyTailCalls returns (Truth, [CpsExp]) 
        -- but we only care about the Truth here.
        check = testFromSource $ \e bs -> fst $ onlyTailCalls e bs

refersToTests :: TestTree
refersToTests = testGroup "refersTo" $ map check
  [ ("simple contains", ["x"], "x", True)
  , ("simple does not contain", ["x"], "y", False)
  , ("contains superstring", ["x"], "xy", False)
  , ("contains in app", ["x"], "foo x", True)
  , ("contains in case scrut", ["bar"], "case bar of () -> ()", True)
  , ("contains in case branch", ["baz"], "case () of () -> baz", True)
  , ("contains in lambda body", ["x"], "\\() -> x", True)
  , ("contains in let binding", ["x"], "let foo = x in foo", True)
  , ("contains in let body", ["x"], "let foo = y in foo x", True)
  , ( "does not contain shadowed (case)", ["foo"]
    , "case () of foo -> foo", False)
  , ( "does not contain shadowed (lambda)", ["omega"]
    , "\\omega -> omega omega", False)
  , ( "does not contain shadowed (let 1)", ["foo"]
    , "let foo = x in foo", False)
  , ( "does not contain shadowed (let 2)", ["omega"]
    , "let omega = omega omega in 0", False)
  , ("contains several", ["x", "y"], "case () of () -> x; () -> y", True)
  , ("contains some but not all", ["foo", "bar"], "(0, foo)", True)
  , ("contains none", ["foo", "bar", "baz"], "x ()", False)
  ]
  where check = testFromSource refersTo

-- this one doesn't test mutual recursion
cpsTailRecursiveTests :: TestTree
cpsTailRecursiveTests = testGroup "cpsTailRecursive" $ map check
  [ ("simple holds", "go acc [] = acc\ngo acc (x:xs) = go (x:acc) xs", Holds)
  , ("simple vacuous", "rev = reverse", Vacuous)
  , ("simple fails", "rev = const reverse $ rev", Fails)
  , ( "local binding holds"
    , "rev = go [] where\n  go acc [] = acc\n  go acc (x:xs) = go (x:acc) xs"
    , Holds)
  , ( "tail recursive map"
    , unlines [ "map f = reverse . go [] where" -- note 'go' not tail called
              , "  go acc [] = acc"
              , "  go acc (x:xs) = go (f x : acc) xs" ]
    , Holds)
  , ( "nested local"
    , unlines [ "foo = go [] where"
              , "  go = bar where"
              , "    bar acc [] = acc"
              , "    bar acc (x:xs) = bar (x:acc) xs" ]
    , Holds)
  , ("direct recursive local", "foo = bar where bar = 0:bar", Fails)
  , ( "complex direct recursive local"
    , unlines [ "filter p = go where"
              , "  go [] = []"
              , "  go (x:xs) | p x = x : go xs"
              , "            | otherwise = go xs" ]
    , Fails)
  , ( "good and bad locals"
    , unlines [ "filter p = good [] where"
              , "  good acc [] = acc"
              , "  good acc (x:xs) | p x = good (x:acc) xs"
              , "                  | otherwise = good acc xs"
              , "  bad [] = []"
              , "  bad (x:xs) | p x = x : bad xs"
              , "             | otherwise = bad xs" ]
    , Fails)
  ]
  where check (desc, src, expected) =
          let Binding name _ body = processDecl src
          in testCase desc $ expected @=? cpsTailRecursive body [name]