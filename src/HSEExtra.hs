{-
This module exports extra functions and things that we need on top of
haskell-src-exts. Part of separating the functionality into modules
means that several modules need access to 'HasName' and also we need
an orphan Plated instance so it belongs here too.
-}

{-# LANGUAGE FlexibleInstances #-}
module HSEExtra where

import Control.Lens.Plated (Plated)
import Data.Functor (void)
import Data.Data (Data)

import qualified Language.Haskell.Exts as HS

-- enables the use of 'cosmos'
instance Data ann => Plated (HS.Exp ann)

class HasName a where
  flatName :: a -> String

instance HasName String where flatName = id

instance HasName (HS.Name ann) where
  flatName (HS.Ident _ name)  = name
  flatName (HS.Symbol _ name) = name

instance HasName (HS.QName ann) where
  flatName (HS.Qual _ (HS.ModuleName _ m) n) = m ++ "." ++ flatName n
  flatName (HS.UnQual _ n) = flatName n
  flatName (HS.Special _ special) = case special of
    HS.UnitCon _ -> "()"
    HS.ListCon _ -> "[]"
    HS.Cons _    -> ":"
    HS.TupleCon _ HS.Boxed n -> "(" ++ replicate (n-1) ',' ++ ")"
    -- other things should only appear in types as far as I can tell.
    other -> error $ "flatName@QName: can't handle " ++ 
                     show (void other)

instance HasName (HS.QOp ann) where
  flatName (HS.QVarOp _ name) = flatName name
  flatName (HS.QConOp _ name) = flatName name
