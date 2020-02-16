{-# LANGUAGE MultiParamTypeClasses
           , FlexibleContexts
           , AllowAmbiguousTypes
           , FlexibleInstances #-}

module Lib where

import Debug.Trace
import Language.Haskell.Exts
import Data.IORef

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

---- cps checker, tail/forward recursion checkers
type Counter = Int -> IO Int
makeCounter :: IO Counter
makeCounter = do
      r <- newIORef 0
      return (\i -> do modifyIORef r (+i)
                       readIORef r)


data Const = IntConst Int | BoolConst Bool | StringConst String |FloatConst Float
  | UserDefConst String | NilConst | UnitConst deriving ( Eq, Show, Ord )

data ThisPat = WildPat | ConstPat Const
  | VarPat String | TuplePat ThisPat ThisPat | ConstrPat String ThisPat deriving ( Eq, Show, Ord )

data ContVar = Kvar Int deriving ( Eq, Show, Ord )

data MonOp = IntNegOp | NotOp deriving ( Eq, Show, Ord )

data BinOp = IntPlusOp
  | IntMinusOp
  | IntTimesOp
  | IntDivOp
  | IntModOp
  | FloatPlusOp
  | FloatMinusOp
  | FloatTimesOp
  | FloatDivOp
  | FloatExpOp
  | ListCatOp
  | StringCatOp
  | GtOp
  | LtOp
  | GeOp
  | LeOp
  | EqOp
  | NeqOp
  | AndOp
  | OrOp
  | SeqOp deriving ( Eq, Show, Ord )

type RegVar = String

data CpsCont = External | ContVarCPS ContVar | FnContCPS ThisPat ExpCps deriving ( Eq, Show, Ord )

data ExpCps = ValueCPS CpsCont ThisPat
 | MonOpAppCPS CpsCont MonOp ThisPat
 | BinOpAppCPS CpsCont BinOp ThisPat ThisPat
 | MatchCPS ThisPat [(ThisPat, ExpCps)]
 | AppCPS CpsCont RegVar ThisPat
 | FunCPS CpsCont ThisPat ContVar ExpCps
 | FixCPS CpsCont RegVar ThisPat ContVar ExpCps deriving ( Eq, Show, Ord )

---pat_pat_match function
pat_pat_match gen_pat spec_pat =
  case gen_pat of
      WildPat -> Just []
      ConstPat c -> (case spec_pat of ConstPat c' -> (if c == c' then Just [] else Nothing)
                                      _ -> Nothing)
      VarPat s -> Just [(s,spec_pat)]
      TuplePat gp1 gp2 -> (case spec_pat of TuplePat sp1 sp2 -> (pat_pat_match gp1 sp1) >>= (\a -> (pat_pat_match gp2 sp2) >>= (\b -> return (a ++ b))))
      ConstrPat c gpat -> (case spec_pat
                             of ConstrPat c' spat ->
                                    (if c == c' then pat_pat_match gpat spat else Nothing)
                                _ -> Nothing)
---varsInPat function
varsInPat pat =
  case pat of { WildPat -> []
    ; ConstPat _ -> []
    ; VarPat s -> [s]
    ; TuplePat p1 p2 -> ((varsInPat p1) ++ (varsInPat p2))
    ; ConstrPat c p -> varsInPat p}

----map_rm fun
map_rm f x =
  case f of
    [] -> []
    (a, b):r -> if x == a then r else (a,b):(map_rm r x)

---map ins function
map_ins f x y =
  case f of
    [] -> [(x, y)]
    ((a, b)):r -> if x == a then (x, y):r else (a,b):(map_ins r x y)

---map_merge fun
map_merge f g =
  case f of
    [] -> g
    (a, b):r -> map_merge r (map_ins g a b)

merge l1 l2 =
  case (l1,l2) of
  ([],l) -> l
  (l,[]) -> l
  (h1:t1,h2:t2) ->
    if h1 < h2  then h1:(merge t1 l2)
    else if h2 < h1 then h2:(merge l1 t2)
    else merge t1 l2

map_find f x =
  case f of
    [] -> Nothing
    (a, b):r -> (if x == a then Just b else map_find r x)

fresh counter = (show counter, counter + 1)

swap_vars_in_pat x y pat =
  case pat
  of WildPat -> WildPat 
     ConstPat c -> pat
     VarPat s -> VarPat (if s == x then y else if s == y then x else s)
     TuplePat p1 p2 -> TuplePat (swap_vars_in_pat x y p1) (swap_vars_in_pat x y p2)
     ConstrPat c p -> ConstrPat c (swap_vars_in_pat x y p)

replace_var_in_pat x y pat =
  case pat
  of WildPat -> WildPat
     ConstPat c -> pat
     VarPat s -> VarPat (if s == x then y else s)
     TuplePat p1 p2  -> TuplePat (replace_var_in_pat x y p1) (replace_var_in_pat x y p2)
     ConstrPat c p -> ConstrPat c (replace_var_in_pat x y p)

swap_vars_in_cps_cont x y k =
  (case k of
      External -> k
      ContVarCPS _ -> k
      FnContCPS p e ->
         (case swap_vars_in_clause_cps x y (p, e)
                 of (p',e') -> FnContCPS p' e'))
swap_vars_in_cps_exp x y e = (
  case e
  of  ValueCPS k p -> ValueCPS (swap_vars_in_cps_cont x y k) (swap_vars_in_pat x y p)
      MonOpAppCPS k m s ->  MonOpAppCPS (swap_vars_in_cps_cont x y k) m (swap_vars_in_pat x y s)
      BinOpAppCPS k b r s -> BinOpAppCPS (swap_vars_in_cps_cont x y k) b (swap_vars_in_pat x y r) (swap_vars_in_pat x y s)
      MatchCPS s kcls  -> MatchCPS (swap_vars_in_pat x y s) (map (\ kcl -> (swap_vars_in_clause_cps x y kcl)) kcls)
      AppCPS k r s -> AppCPS (swap_vars_in_cps_cont x y k) (if r == x then y else if r == y then x else r)
                                            (swap_vars_in_pat x y s)
      FunCPS k p kv e -> FunCPS (swap_vars_in_cps_cont x y k) (swap_vars_in_pat x y p) kv (swap_vars_in_cps_exp x y e)
      FixCPS  k f p kv e -> FixCPS (swap_vars_in_cps_cont x y k)
                                    (if f == x then y else if f == y then x else f)
                                       (swap_vars_in_pat x y p) kv (swap_vars_in_cps_exp x y e))
swap_vars_in_clause_cps x y (p,e) =
  (swap_vars_in_pat x y p, swap_vars_in_cps_exp x y e)

replace_var_in_cps_cont x y k =
  (case k of 
      External -> k
      ContVarCPS _ -> k
      FnContCPS p e ->
           (case replace_var_in_clause_cps x y (p, e)
                             of (p', e') -> FnContCPS p'  e'))
replace_var_in_cps_exp x y e = (
  case e
  of ValueCPS k p -> ValueCPS (replace_var_in_cps_cont x y k) (replace_var_in_pat x y p)
     MonOpAppCPS k m s ->
           MonOpAppCPS (replace_var_in_cps_cont x y k) m (replace_var_in_pat x y s)
     BinOpAppCPS k b r s ->
             BinOpAppCPS (replace_var_in_cps_cont x y k) b (replace_var_in_pat x y r)
                                (replace_var_in_pat x y s)
     MatchCPS s kcls ->
          MatchCPS (replace_var_in_pat x y s)
                 (map (\ kcl -> (replace_var_in_clause_cps x y kcl)) kcls)
     AppCPS k r s ->
         AppCPS (replace_var_in_cps_cont x y k) (if r == x then y else r) (replace_var_in_pat x y s)
     FunCPS k p kv e -> 
          (case replace_var_in_clause_cps x y (p,e) of (p',e') -> FunCPS (replace_var_in_cps_cont x y k) p' kv e')
     FixCPS k f p kv e -> (case replace_var_in_clause_cps x y (TuplePat (VarPat f) p, e)
                              of (TuplePat  (VarPat f') p' , e') ->
                                                   FixCPS (replace_var_in_cps_cont x y k) f' p' kv e'))
replace_var_in_clause_cps x y (pat, e) = 
  let pat_vars = varsInPat pat
  in if elem x pat_vars then (pat, e)
    else if elem y pat_vars
    then (swap_vars_in_pat x y pat, swap_vars_in_cps_exp x y e)
    else (pat, replace_var_in_cps_exp x y e)

rename_away_clause_cps fs (bnd_pat, e) counter =
  let capture_vars = filter (\ v -> elem v fs) (varsInPat bnd_pat) in
    foldl
      (\ (bpat,e',count) -> (\ bvar ->
        let new_bvar = fst (fresh count) in
          (replace_var_in_pat bvar new_bvar bpat, replace_var_in_cps_exp bvar new_bvar e' , snd (fresh count))))
      (bnd_pat,e,counter)
      capture_vars

subst_vars_by_pats_in_pat subst gen_pat =
  case gen_pat of
     WildPat -> WildPat
     ConstPat c -> gen_pat
     VarPat s -> (case map_find subst s of Nothing -> gen_pat
                                           Just spec_pat -> spec_pat)
     TuplePat p1 p2 ->
      TuplePat (subst_vars_by_pats_in_pat subst p1)
                (subst_vars_by_pats_in_pat subst p2)
     ConstrPat c p -> ConstrPat c (subst_vars_by_pats_in_pat subst p)

---subst_vars_by_pats_in_cps_cont
subst_vars_by_pats_in_cps_cont subst k counter =
  case k of 
      External -> (k,counter)
      ContVarCPS _ -> (k,counter)
      FnContCPS p e ->
           (case subst_vars_by_pats_in_clause_cps subst (p, e) counter
                         of ((p', e'),counter') -> (FnContCPS p' e',counter'))
---  subst_vars_by_pats_in_cps_exp
subst_vars_by_pats_in_cps_exp subst e counter = 
  case e
  of {ValueCPS k p ->
        (case (subst_vars_by_pats_in_cps_cont subst k counter) of (newk,newcounter) -> (ValueCPS newk (subst_vars_by_pats_in_pat subst p),newcounter))
      ;MonOpAppCPS k m s -> (case subst_vars_by_pats_in_cps_cont subst k counter of (newk, newcounter) -> (MonOpAppCPS newk m (subst_vars_by_pats_in_pat subst s), newcounter))
      ;BinOpAppCPS k b r s -> (case subst_vars_by_pats_in_cps_cont subst k counter of (newk, newcounter) -> (BinOpAppCPS newk b (subst_vars_by_pats_in_pat subst r) (subst_vars_by_pats_in_pat subst s), newcounter))
      ;MatchCPS s kcls -> (case foldr (\ kcl -> (\ (res,count) -> (case subst_vars_by_pats_in_clause_cps subst kcl count
                                                              of (newkcl,newCount) -> ((newkcl:res),newCount))))
                               ([],counter) kcls
                           of  (newkcls,newcounter) -> (MatchCPS (subst_vars_by_pats_in_pat subst s) newkcls, newcounter))
      ;AppCPS k r pat -> (case subst_vars_by_pats_in_cps_cont subst k counter
                               of (newk,newCounter) -> (AppCPS newk
                                                             (case map_find subst r of Nothing -> r
                                                                                       Just (VarPat r') -> r') (subst_vars_by_pats_in_pat subst pat), newCounter))
       ;FunCPS k p kv e -> (case subst_vars_by_pats_in_clause_cps subst (p,e) counter
                              of ((p',e'),newCounter) -> (case subst_vars_by_pats_in_cps_cont subst k newCounter
                                                        of (newk,newC) -> (FunCPS newk p' kv e',newC)))
       ;FixCPS k f p kv e -> (case subst_vars_by_pats_in_clause_cps subst (TuplePat (VarPat f) p, e) counter
          of ((TuplePat (VarPat f') p', e'),newC) -> (case subst_vars_by_pats_in_cps_cont subst k newC
                                                        of (newkk,newCC) -> (FixCPS newkk f' p' kv e',newCC)))}
---subst_vars_by_pats_in_clause_cps
subst_vars_by_pats_in_clause_cps subst (bnd_pat, e) counter =
  let bnd_vars = varsInPat bnd_pat in
  let thinned_subst = foldl map_rm subst bnd_vars in
  let redex_vars = foldl (\ vars -> \ (_,spec_pat) -> (merge (varsInPat spec_pat) vars)) [] thinned_subst
  in
  let capture_vars = filter (\ v -> elem v redex_vars) bnd_vars in
  let (alpha_bnd_pat, alpha_e,counter') = rename_away_clause_cps capture_vars (bnd_pat, e) counter
  in
   (case subst_vars_by_pats_in_cps_exp subst alpha_e counter' of (newk,newC) -> ((alpha_bnd_pat, newk), newC))


mkValueCPS (k, spec_pat) counter =
  case k
  of FnContCPS gen_pat e -> (case pat_pat_match gen_pat spec_pat
                             of Nothing -> Nothing
                                Just subst -> 
                                 (case subst_vars_by_pats_in_cps_exp subst e counter of (newk,newC) -> Just (ValueCPS k spec_pat)))
     _ -> Just (ValueCPS k spec_pat)

---- cps transformation
cpsExp (Var x y) k = k (Var x) 

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
