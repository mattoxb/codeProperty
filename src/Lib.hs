{-# LANGUAGE MultiParamTypeClasses
           , FlexibleContexts
           , AllowAmbiguousTypes
           , FlexibleInstances #-}

module Lib where

import Debug.Trace
import Language.Haskell.Exts

class HasExpChildren a b where
  expChildren :: a -> [Exp b]

instance HasExpChildren (Exp t) t where
  expChildren (InfixApp _ e1 _ e2) = [e1,e2]
  expChildren (App _ e1 e2) = [e1,e2]
  expChildren (NegApp _ e1) = [e1]
  expChildren (Lambda _ _ e1) = [e1]
  expChildren (Let _ binds e1) = undefined -- Need to recurse binds
  expChildren (If _ e1 e2 e3) = [e1,e2,e3]
  expChildren (Case _ e1 alts) = undefined -- need to recurse alts
  expChildren (Tuple _ _ ee) = ee
  expChildren (UnboxedSum _ _ _ e1) = [e1]
  expChildren (TupleSection _ _ mes) = undefined -- Need to recurse mes :: [Maybe (Exp l)]
  expChildren (List _ es) = es
  expChildren (ParArray _ es) = es
  expChildren (Paren _ e1) = [e1]
  expChildren (LeftSection _ e1 _) = [e1]
  expChildren (RightSection _ _ e1) = [e1]
  expChildren (EnumFrom _ e1) = [e1]
  expChildren (EnumFromTo _ e1 e2) = [e1,e2]
  expChildren (EnumFromThen _ e1 e2) = [e1,e2]
  expChildren (EnumFromThenTo _ e1 e2 e3) = [e1,e2,e3]
  expChildren (ParArrayFromTo _ e1 e2) = [e1,e2]
  expChildren (ParArrayFromThenTo _ e1 e2 e3) = [e1,e2,e3]
  expChildren (ListComp _ e1 q) = e1 : expChildren q
  expChildren (ParComp _ e1 q) = e1 : concatMap expChildren q
  expChildren (ParArrayComp _ e1 q) = e1 : concatMap expChildren q
  expChildren (ExpTypeSig _ e1 _) = [e1]
  expChildren (SpliceExp _ s) = expChildren s
  expChildren (XTag _ _ _ Nothing es) = es
  expChildren (XTag _ _ _ (Just e1) es) = e1:es
  expChildren (XETag _ _ _ (Just e1)) = [e1]
  expChildren (XExpTag _ e1) = [e1]
  expChildren (XChildTag _ es) = es
  expChildren (CorePragma _ _ e1) = [e1]
  expChildren (SCCPragma _ _ e1) = [e1]
  expChildren (GenPragma _ _ _ _ e1) = [e1]
  expChildren (Proc _ _ e1) = [e1]
  expChildren (LeftArrApp _ e1 e2) = [e1,e2]
  expChildren (RightArrApp _ e1 e2) = [e1,e2]
  expChildren (LeftArrHighApp _ e1 e2) = [e1,e2]
  expChildren (RightArrHighApp _ e1 e2) = [e1,e2]
  expChildren (LCase _ _) = undefined
  expChildren (Do _ _) = undefined
  expChildren (MDo _ _) = undefined
  expChildren (RecConstr _ _ _) = undefined
  expChildren (RecUpdate _ _ _) = undefined
  expChildren (BracketExp _ _) = undefined
  expChildren _ = []

instance HasExpChildren (QualStmt p) p where
  expChildren (QualStmt _ s) = expChildren s
  expChildren (ThenTrans _ e1) = [e1]
  expChildren (ThenBy _ e1 e2) = [e1,e2]
  expChildren (GroupBy _ e1) = [e1]
  expChildren (GroupUsing _ e1) = [e1]
  expChildren (GroupByUsing _ e1 e2) = [e1,e2]

instance HasExpChildren (m a) a => HasExpChildren [m a] a where
  expChildren xx = concatMap expChildren xx

instance HasExpChildren (m a) a => HasExpChildren (Maybe (m a)) a where
  expChildren Nothing = []
  expChildren (Just x) = expChildren x

instance HasExpChildren (Maybe (Exp a)) a where
  expChildren Nothing = []
  expChildren (Just x) = [x]

instance HasExpChildren (Stmt l) l where
  expChildren (Generator _ pat e1) = [e1]
  expChildren (Qualifier _ e1) = [e1]
  expChildren (LetStmt _ binds) = []
  expChildren (RecStmt _ xx) = expChildren xx

instance HasExpChildren (Binds l) l where
  expChildren (BDecls _ decls) = expChildren decls
  expChildren (IPBinds _ ipbinds) = expChildren ipbinds

instance HasExpChildren (IPBind l) l where
  expChildren (IPBind _ _ e1) = [e1]

instance HasExpChildren (Decl l) l where
  expChildren (FunBind _ matches) = expChildren matches
  expChildren (PatBind _ pat rhs mbinds) = expChildren rhs ++ expChildren mbinds

instance HasExpChildren (Match l) l where
  expChildren (Match _ _ pats rhs mbinds) = expChildren rhs ++ expChildren mbinds
  expChildren (InfixMatch _ pats1 _ pats2 rhs mbinds) = expChildren rhs ++ expChildren mbinds

instance HasExpChildren (Rhs l) l where
  expChildren (UnGuardedRhs _ e1) = [e1]
  expChildren (GuardedRhss _ guardedRhs) = concatMap expChildren guardedRhs

instance HasExpChildren (GuardedRhs l) l where
  expChildren (GuardedRhs _ ss e) = expChildren ss ++ expChildren e

instance HasExpChildren (Splice l) l where
  expChildren (ParenSplice _ e) = [e]
  expChildren _ = []

ex1 = "fact 0 = 1\nfact n = n * fact (n-1)\n"
ex2 = "fact n | n == 0 = 1\nfact n = n * fact (n-1)\n"
ex3 = "fact n = product [1..n]"
ex4 = "fact n = aux n 0\n  where aux 0 a = a\n        aux n a = aux (n-1) (a*n)"
ex5 = "fact n = aux n 0\n  where aux 0 a = 1\n        aux n a = n * aux (n-1) (a*n)"
ex6 = "fact n = aux n 0\n  where aux 0 a = 1\n        aux n a = n * fact (n-1)"

someFunc :: IO ()
someFunc = putStrLn "someFunc"

isRecursive :: [String] -> Decl b -> Bool
isRecursive names (FunBind _ matches) = any (aux names) matches

aux :: [String] -> Match l -> Bool
aux names (Match _ (Ident _ name) pats rhs bd) =
  any (recursiveCall (name:names)) (ec rhs) ||
  case bd of
    Nothing -> False
    Just (BDecls _ decls) -> any (isRecursive (name:names)) decls
  where ec :: Rhs l -> [Exp l]
        ec = expChildren 

-- recursiveCall :: [String] -> Exp l -> Bool
recursiveCall names (App _ (Var _ (UnQual _ (Ident _ n2))) _) = trace ("App " ++ n2 ++ " " ++ show names) elem n2 names
recursiveCall names (InfixApp _ a (QVarOp _ (UnQual _ (Ident _ n2))) b) = elem n2 names
recursiveCall names (Let _ (BDecls _ decls) e1) = any (isRecursive names) decls || recursiveCall names e1
recursiveCall names e = any (recursiveCall names) (ec e)
  where ec :: Exp l -> [Exp l]
        ec = expChildren

check x = let ParseOk y = parseDecl x in isRecursive [] y

factp :: Decl ()
factp =
 (FunBind ()
  [Match () (Ident () "fact") [PVar () (Ident () "n")]
   (GuardedRhss () [GuardedRhs () [Qualifier ()
                                       (InfixApp ()
                                        (Var () (UnQual () (Ident () "n")))
                                        (QVarOp () (UnQual () (Symbol () "==")))
                                        (Lit () (Int () 0 "0")))]
                       (Lit () (Int () 1 "1"))]) Nothing
  ,Match () (Ident () "fact") [PVar () (Ident () "n")]
   (UnGuardedRhs ()
    (InfixApp ()
     (Var () (UnQual () (Ident () "n")))
     (QVarOp () (UnQual () (Symbol () "*")))
      (App ()
        (Var () (UnQual () (Ident () "fact")))
        (Paren () (InfixApp ()
                     (Var () (UnQual () (Ident () "n")))
                     (QVarOp () (UnQual () (Symbol () "-")))
                     (Lit () (Int () 1 "1"))))))) Nothing])

pex3 = (InfixApp ()
     (Var () (UnQual () (Ident () "n")))
     (QVarOp () (UnQual () (Symbol () "*")))
      (App ()
        (Var () (UnQual () (Ident () "fact")))
        (Paren () (InfixApp ()
                     (Var () (UnQual () (Ident () "n")))
                     (QVarOp () (UnQual () (Symbol () "-")))
                     (Lit () (Int () 1 "1"))))))
