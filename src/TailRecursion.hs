module TailRecursion where

import CPS

import Control.Lens.Fold (anyOf)
import Data.Data.Lens (biplate)

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