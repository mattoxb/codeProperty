module ContainsListComp (containsListComp) where

import Control.Lens.Fold (anyOf)
import Control.Lens.Plated (cosmos)
import Data.Data (Data)
import HSEExtra ()

import Language.Haskell.Exts.Syntax (Exp (ListComp))

isListComp :: Exp ann -> Bool
isListComp ListComp {} = True
isListComp _ = False

-- | Does exactly what it says on the tin.
containsListComp :: Data ann => Exp ann -> Bool
containsListComp = anyOf cosmos isListComp

-- 'anyOf cosmos' is basically black magic. If you haven't seen lens before,
-- it's probably easier to think about 'any isListComp . universe' which
-- is equivalent but a bit less efficient (lens is highly optimized).
-- 'universe' would take an Exp and return a list of all of the transitively
-- contained Exps (including itself).
