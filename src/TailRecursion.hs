module TailRecursion where

import CPS

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