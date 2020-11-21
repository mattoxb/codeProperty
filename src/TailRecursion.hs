module TailRecursion where

import CPS

import Control.Lens.Fold (anyOf)
import Data.Data.Lens (biplate)

-- | Determine if the given CpsExp only refers to the given binders
-- in tail positions. In other words, all references are tail references.
-- If the CpsExp hasn't been renamed, this WILL think local bindings that
-- shadow free variables are the same raw binder!
--
-- Does not recurse into local bindings.
--
-- It is assumed that the CpsExp came from the CPS Transform of some real
-- Haskell code, and therefore all ContVars are the local continuation
-- at that point in the expression. That means that outside of a lambda,
-- anything with a VarCont continuation is in tail position.
onlyTailCalls :: CpsExp -> [Binder] -> Bool
onlyTailCalls exp binders = go exp
  where
    go (SimpleExpCps se (VarCont _)) = True
    go (SimpleExpCps se (FnCont _ ke)) =
      safe se && go ke
    go (MatchCps se cs) =
      safe se && all go (map snd cs) -- patterns can't refer to things
    go (AppCps head args (VarCont _)) =
      -- the head can be anything; if it is one of the targets, then it's
      -- in tail position. If it isn't a target, we don't care.
      all safe args
    go (AppCps head args (FnCont _ ke)) =
      all safe (head : args) && go ke
    go (LamCps _ _ body k) = not (body `refersTo` binders) && goCont k
      where goCont (VarCont _) = True
            goCont (FnCont _ ke) = go ke

    safe = (`notElem` map Var binders)

-- | Determine if the given CpsExp refers to ANY of the given raw binders
-- in any position anywhere in the structure.
--
-- This isn't sufficient to detect recursive functions because while
-- it will find local definitions that refer to a given name, it won't
-- find an auxiliary function that refers to itself.
refersTo :: CpsExp -> [Binder] -> Bool
refersTo e bs = anyOf biplate (`elem` map Var bs) e
