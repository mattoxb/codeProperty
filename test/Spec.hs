import Test.Tasty
import Test.Tasty.HUnit

import qualified Language.Haskell.Exts.Parser as Parse

import CPS
import TailRecursion

-- I'd like to write a property test like
-- prop_renameLeavesFvs exp = sort (alLRawBinders (renameExp exp)) == freeVars exp
-- but I really don't know how to make a good Arbitrary instance for CpsExp.

main :: IO ()
main = defaultMain hunitTests

hunitTests :: TestTree
hunitTests = testGroup "HUnit tests"
  [ refersToTests
  , onlyTailCallsNoLetTests
  , cpsTailRecursiveTests
  ]

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

processDecl :: String -> CpsBinding
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
          let binding = processDecl src
          in testCase desc $ expected @=? bindingTailRecursive binding
