{-# LANGUAGE ScopedTypeVariables #-}
module ContainsListComp (containsListComp) where

import Data.Data.Lens (biplate)
import Control.Lens (Traversal')
import Control.Lens.Fold (anyOf)
import Control.Lens.Plated (cosmos)
import Data.Data (Data)
import HSEExtra ()

import Language.Haskell.Exts.Syntax (Module, Exp (ListComp))

isListComp :: Exp ann -> Bool
isListComp ListComp {} = True
isListComp _ = False

-- | Does exactly what it says on the tin.
expContainsListComp :: Data ann => Exp ann -> Bool
expContainsListComp = anyOf cosmos isListComp

-- | Test if a 'Module' contains any list comprehensions.
containsListComp :: forall ann. Data ann => Module ann -> Bool
containsListComp = anyOf traverseExps expContainsListComp
  where
    -- scoped type variables is necessary in order for the 'Data ann'
    -- constraint to propogate to 'Exp ann'.
    traverseExps :: Traversal' (Module ann) (Exp ann)
    traverseExps = biplate

-- 'anyOf cosmos' is basically black magic. If you haven't seen lens before,
-- it's probably easier to think about 'any isListComp . universe' which
-- is equivalent but a bit less efficient (lens is highly optimized).
-- 'universe' would take an Exp and return a list of all of the transitively
-- contained Exps (including itself).
