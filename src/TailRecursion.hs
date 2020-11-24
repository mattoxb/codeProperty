module TailRecursion where

import CPS

import Control.Lens.Fold (anyOf)
import Data.Data.Lens (biplate)

-- | TODO: I think everything gets cleaner if 'onlyTailCalls' recurses
-- into the LetCps _body_ but not the bindings themselves. Even the current
-- version would perhaps get somewhat cleaer.
-- Then with fgl:
-- we simply extract every single binding in an entire module, construct
-- the call graph, compute the condensation, and for each binding, its body
-- 'onlyTailCalls' the other bindings in its SCC.
-- An entire SCC is bad if any single binding in the SCC is bad or if any
-- binding in the SCC calls a binding in a bad SCC.

data Truth
  = Holds
  | Vacuous
  | Fails
  deriving (Eq, Show)

-- | This is kind of like 'And' from Data.Monoid
instance Semigroup Truth where
  Fails   <> _       = Fails
  _       <> Fails   = Fails
  Vacuous <> Vacuous = Vacuous
  _       <> _       = Holds

instance Monoid Truth where
  mempty = Vacuous

holds :: Truth -> Bool
holds Holds = True
holds _     = False

-- | Determine if the given CpsExp only refers to the given binders
-- in tail positions. In other words, all references are tail references.
--
-- On encountering a LetCps node, the function stops. The return value may
-- indicate that there are LetCps nodes to inspect further (though there
-- is no need if we already know that the check Fails).
-- This is because local bindings indicate that we need to change the set
-- of names that we're looking for, and is more versatile with respect to
-- handling mutual recursion.
--
-- It is assumed that the CpsExp came from the CPS Transform of some real
-- Haskell code, and therefore all ContVars are the local continuation
-- at that point in the expression. That means that outside of a lambda,
-- anything with a VarCont continuation is in tail position.
-- Furthermore assuems that the exp has been renamed. This is not checked.
onlyTailCalls :: CpsExp -> [Binder] -> (Truth, [CpsExp])
onlyTailCalls exp binders = go exp
  where
    go :: CpsExp -> (Truth, [CpsExp])
    go (SimpleExpCps se (VarCont _)) = guardTarget (target se)
    go (SimpleExpCps se (FnCont _ ke)) = guardSafe (safe se) <> go ke
    go (MatchCps se cs) =
      -- patterns can't refer to things
      guardSafe (safe se) <>  foldMap go (map snd cs)
    go (AppCps head args (VarCont _)) =
      guardTarget (target head) <> guardSafe (all safe args)
    go (AppCps head args (FnCont _ ke)) =
      guardSafe (all safe (head : args)) <> go ke
    -- If the lambda is in tail position, that means the lambda's body is
    -- actually part of the full-arity body of expression, so we should check
    -- it as though it were part of the body.
    go (LamCps _ _ body (VarCont _)) = go body
    -- we aggressively suppose that tail recursion is not possible from inside
    -- a lambda which is not in tail position. I'm not convinced that this is
    -- actually the case; however any tail-recursive code that does this is
    -- so egregious that it should honestly be rejected anyway.
    go (LamCps _ _ body (FnCont _ ke)) = 
      guardSafe (not $ body `refersTo` binders) <> go ke
    -- This function is not concerned with what happens inside local bindings.
    -- See the documentation.
    go e@LetCps{} = (Vacuous, [e])

    targets = map Var binders
    target = (`elem` targets)
    safe = (`notElem` targets)

guardSafe :: Bool -> (Truth, [a])
guardSafe True  = (Vacuous, [])
guardSafe False = (Fails,   [])

guardTarget :: Bool -> (Truth, [a])
guardTarget True  = (Holds,   [])
guardTarget False = (Vacuous, [])

-- | Determine if the given CpsExp refers to ANY of the given raw binders
-- in any position anywhere in the structure.
--
-- This isn't sufficient to detect recursive functions because while
-- it will find local definitions that refer to a given name, it won't
-- find an auxiliary function that refers to itself.
refersTo :: CpsExp -> [Binder] -> Bool
refersTo e bs = anyOf biplate (`elem` map Var bs) e

bindRefersTo :: CpsBinding -> [Binder] -> Bool
bindRefersTo (Binding _ _ body) = refersTo body

cpsTailRecursive :: CpsExp -> [Binder] -> Truth
cpsTailRecursive e bs = case onlyTailCalls e bs of
    (Fails, _)    -> Fails
    (truth, [])   -> truth
    (truth, lcls) -> goLocals truth lcls
  where
    goLocals truth lcls = truth <> foldMap goLocal lcls
    goLocal (LetCps bindings body) = localsTailRecursive bindings body bs
    goLocal _ = error "goLocal: exp is not a LetCps"

localsTailRecursive :: [CpsBinding] -> CpsExp -> [Binder] -> Truth
localsTailRecursive bindings lbody bndrs = 
  mconcat bindingTruths <> cpsTailRecursive lbody bndrs
  where
    bsWithTruth = map (toSnd goBinding) bindings
    -- handing down the rest of the binders here is kind of a naive mutual
    -- recursion check, so a full & proper mutual recursion check should
    -- probably _replace_ that, rather than only adding new code.
    goBinding (Binding bndr _ body) = cpsTailRecursive body (bndr:bndrs)

    bindingTruths = map snd bsWithTruth

-- | Check if a CpsBinding is tail recursive. We define tail recursive as
-- "the function **or a local binding** is recursive and all recursive calls
-- are tail calls."
--
-- Currently, can be fooled by mutual recursion (may return Vacuous when
-- Holds is expected). Additionally, can theoretically be fooled by an
-- unused tail recursive local binding combined with a call to a
-- non-tail-recursive function bound elsewhere. Therefore, it is a good
-- idea to analyze the whole module, and reject if any bindings Fail the
-- check. However I'm not implementing that at the moment because mutual
-- recursion pieces would likely create a more elegant solution to the same
-- problem.
bindingTailRecursive :: CpsBinding -> Truth
bindingTailRecursive (Binding name _ body) = cpsTailRecursive body [name]

-- tailRecursiveInModule :: [CpsBinding] -> Name -> Bool
-- TODO: implement this either with or without call graph analysis.

toSnd :: (a -> b) -> a -> (a, b)
toSnd f x = (x, f x)