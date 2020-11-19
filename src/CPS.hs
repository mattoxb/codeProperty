{-# LANGUAGE TupleSections #-}

module CPS where

import Errors
import HSEExtra

import           Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE

import Control.Monad.State.Strict

import qualified Language.Haskell.Exts as HS

type Name = String
type Op   = Name

-- | a fresh name generated during CPS or tail recursion
-- detection. Differentiating between these and source Vars
-- is not strictly necessary but allows us to worry less
-- while detecting tail recursion :)
data Unique = Unique Name !Int
  deriving Eq

-- | A Simple Expression in CPS.
-- Variable names are preserved to detect alpha-capture later.
-- If a value is a constant, we really don't care what it is.
data SimpleExp 
  = Const 
  | Var Name 
  | Unq !Unique
  deriving Eq

-- We don't care about the transform being exactly correct in terms
-- of the shapes of patterns (esp. w.r.t to how functions are actually
-- applied) because we're never going to run the code. But we _do_ need
-- to know the names of the binders in lambdas. Thus it's OK to, for
-- example, translate [1, 2, x] as 
-- ConstrPat "[]" [ConstPat, ConstPat, VarPat "x"].
data CpsPat
  = ConstPat -- we don't really care about constant values
             -- wildcard pattern is a ConstPat too
  | VarPat Name
  | AsPat  Name CpsPat
  | TuplePat (NonEmpty CpsPat) -- in fact there are always >= 2
  | ConstrPat String [CpsPat] -- constructor name is needed?
    -- pattern "()" needs to be translated as ConstrPat "()" []
  deriving Eq

data ContVar = KVar Int -- distinguishing is convenient for debugging
                        -- but not actually necessary since there's
                        -- no non-local continuations in Haskell
  deriving Eq

data CpsCont
  = VarCont ContVar
  | FnCont Unique CpsExp
  deriving Eq

data CpsExp
  = SimpleExpCps SimpleExp CpsCont -- this should only happen when the entire
                                   -- expression to transform is simple
  | BinOpAppCps SimpleExp Op SimpleExp CpsCont
  | MatchCps SimpleExp [(CpsPat, CpsExp)]
  | AppCps SimpleExp [SimpleExp] CpsCont
  | LamCps CpsPat ContVar CpsExp CpsCont
  deriving Eq

-------------------------------------------------------------------------------
-- CPS Transform
-------------------------------------------------------------------------------

type CPSM = State Int

runCPSMFrom :: Int -> CPSM a -> a
runCPSMFrom = flip evalState

runCPSM :: CPSM a -> a
runCPSM = runCPSMFrom 0

next :: CPSM Int
next = state $ \s -> (s, s+1)
-- by using names that are illegal in Haskell as both operators and vars,
-- we guarantee that there won't be clashes
fresh :: Name -> CPSM Unique
fresh pre = Unique pre <$> next

freshKVar :: CPSM ContVar
freshKVar = KVar <$> next

-- | Test if an expression is "simple"
-- i.e. a variable name or a literal.
-- '()' is simple, '[]' is simple, but
-- '[1, 2]' is not.
isSimple :: HS.Exp ann -> Bool
isSimple (HS.Var _ _) = True
isSimple (HS.Lit _ _) = True
isSimple (HS.List _ []) = True
isSimple (HS.Con _ _) = True
isSimple _         = False

-- | Convert an HS.Exp that is simple to a 'SimpleExp'.
-- Variable names are preserved, but values of constants
-- are not. See 'SimpleExp'.
asSimpleExp :: HS.Exp ann -> SimpleExp
asSimpleExp (HS.Var _ name) = Var $ flatName name
-- We maybe don't need to keep these names around at all?
asSimpleExp (HS.Con _ name) = Var $ flatName name
asSimpleExp e | isSimple e = Const
              -- might as well play it safe since isSimple is cheap
              | otherwise  = error "asSimpleExp: non-simple argument"

-- | Converts any expression into a simple expression.
-- If the expression is simple as given, it is converted and handed 
-- to the callback. Otherwise, the CPS transform of the expression is
-- taken and a continuation is constructed which hands the resulting
-- simple expression (the value thrown to the continuation) to the callback.
--
-- The argument string is a prefix for the fresh var, if one is needed.
-- That's mostly useful for debugging.
--
-- E.X. 'cpsExp (-e) k' can be expressed as
--  cpsValueM e "v" $ \se -> pure (AppCps (Var "negate") se k)
-- If 'e' is constant this would give AppCps (Var "negate") Const k.
-- If 'e' were, say, 'f x', this would give
--   AppCps (Var "f") (Var "x") $ FN v%1 -> AppCps (Var "negate") (Var v%1) k.
cpsValueM :: HS.Exp ann -> String -> (SimpleExp -> CPSM CpsExp) -> CPSM CpsExp
cpsValueM e pre consumer
  | isSimple e = consumer (asSimpleExp e)
  | otherwise  = do v <- fresh pre
                    contBody <- consumer (Unq v)
                    cpsExp e $ FnCont v contBody

-- | 'cpsValueM', but in this simple case where the consumer is pure.
cpsValue :: HS.Exp ann -> String -> (SimpleExp -> CpsExp) -> CPSM CpsExp
cpsValue e pre consumer = cpsValueM e pre (pure . consumer)

{- Note: [cpsExp Structure]
Below, cases are presented in the same order as the HS.Exp documentation.

Extension-based cases are handled with an explicit error as future proofing.
In practice, haskell-src-exts will give a parse error unless the module being
parsed enables the extension (i.e., it behaves correctly but is unaware of
default-extensions). We (CS 421 @ UIUC) don't enable extensions, so those
cases should not arise.
-}

-- | Monadic CPS Transformation. I haven't written down a formalization
-- of the specific CPS transformation being used, perhaps I should.
-- It isn't semantics preserving; continuations are passed to partial
-- applications in places where they aren't added to function definitions,
-- etc. The important thing is that it does preserve order of evaluation,
-- if the Haskell code were actually code in a strict language like OCaml.
cpsExp :: HS.Exp ann -> CpsCont -> CPSM CpsExp
-- covers HS.Var, HS.Lit, HS.List [], '()', and HS.Con
cpsExp e k | isSimple e = pure $ SimpleExpCps (asSimpleExp e) k
cpsExp (HS.OverloadedLabel _ _) _ = unsupported "overloaded label syntax"
cpsExp (HS.IPVar _ _) _ = unsupported "implicit parameters"

cpsExp (HS.InfixApp _ e1 bigName e2) k = 
  cpsValueM e2 "v" $ \v2 -> -- right-to-left evaluation does e2 first
    cpsValueM e1 "v" $ \v1 -> 
      return $ BinOpAppCps v1 name v2 k
  where name = flatName bigName

cpsExp app@(HS.App _ _ _) k = rebuildApp head args k
  where (head, args) = collectApp app

cpsExp (HS.NegApp _ e) k = cpsValue e "v" $ \se -> 
  AppCps (Var "Prelude.negate") [se] k

cpsExp (HS.Lambda _ pats body) k = do
  kvar <- freshKVar
  -- we don't care about how many syntactic arguments the lambda has,
  -- but we do care about what names are present in their patterns
  let cpsPat = asCpsPat $ HS.PTuple undefined HS.Boxed pats
  cpsBody <- cpsExp body $ VarCont kvar
  return $ LamCps cpsPat kvar cpsBody k

cpsExp HS.Let{} k = unsupported "let expression (support coming soon! ^hopefullytm)"

cpsExp (HS.If _ b t f) k = do
  cpsT <- cpsExp t k
  cpsF <- cpsExp f k
  cpsValue b "b" $ \se ->
    MatchCps se [ (ConstPat, cpsT)
                , (ConstPat, cpsF)
                ]

cpsExp HS.MultiIf{} k = unsupported "multi-way if"

cpsExp (HS.Case _ scrut alts) k = 
  cpsValueM scrut "e" $ \se -> do
    cpsAlts <- mapM (\alt -> cpsAlt alt k) alts
    pure $ MatchCps se cpsAlts

-- This one shouldn't be _too_ hard in theory if we want it
cpsExp HS.Do{} k = unsupported "do notation"
-- This one would be difficult.
cpsExp HS.MDo{} k = unsupported "recursive do notation"
cpsExp (HS.Tuple _ HS.Boxed exps) k = cpsMultiExp TupleMEC exps k
cpsExp (HS.Tuple _ HS.Unboxed _)  k = unsupported "unboxed tuple"
cpsExp HS.UnboxedSum{} k = unsupported "unboxed sum"
cpsExp HS.TupleSection{} k = unsupported "tuple section"
cpsExp (HS.List _ exps) k = cpsMultiExp ListMEC exps k
cpsExp HS.ParArray{} k = unsupported "parallel array"
cpsExp (HS.Paren _ e) k = cpsExp e k
-- sections SHOULD be easy, so TODO. They also should be handled by collectApp,
-- but honestly, who writes '(+1) 2' in real code?
cpsExp HS.LeftSection{} k = unsupported "operator section"
cpsExp HS.RightSection{} k = unsupported "operator section"
cpsExp HS.RecConstr{} k = unsupported "record construction"
cpsExp HS.RecUpdate{} k = unsupported "record update"
-- The 'EnumX' family are semantics breaking in the same way as 'List'
-- however we _could_ desugar them easily into
-- Prelude.enumFrom, Prelude.EnumFromTo, etc.
cpsExp (HS.EnumFrom _ e)              k = cpsMultiExp ListMEC [e] k
cpsExp (HS.EnumFromTo _ e1 e2)        k = cpsMultiExp ListMEC [e1, e2] k
cpsExp (HS.EnumFromThen _ e1 e2)      k = cpsMultiExp ListMEC [e1, e2] k
cpsExp (HS.EnumFromThenTo _ e1 e2 e3) k = cpsMultiExp ListMEC [e1, e2, e3] k
cpsExp HS.ParArrayFromTo{}     k = unsupported "parallel array"
cpsExp HS.ParArrayFromThenTo{} k = unsupported "parallel array"
-- What to do in this case is maybe not so clear. Is crashing OK? We DO expect
-- to see these in the wild, but transforming them without desugraing them is
-- basically impossible (because Stmts can be Generators, which bind names).
-- On the other hand, in tail recursion questions, list comps are not allowed,
-- so if the tree was scanned for list comprehensions already, it should be
-- impossible to see one here at all.
cpsExp HS.ListComp{}     k = unsupported "list comprehension during CPS"
cpsExp HS.ParComp{}      k = unsupported "parallel list comprehension"
cpsExp HS.ParArrayComp{} k = unsupported "parallel array comprehension"
cpsExp (HS.ExpTypeSig _ e _) k = cpsExp e k
cpsExp HS.VarQuote{}   k = unsupported "template haskell"
cpsExp HS.TypQuote{}   k = unsupported "template haskell"
cpsExp HS.BracketExp{} k = unsupported "template haskell"
cpsExp HS.SpliceExp{}  k = unsupported "template haskell"
cpsExp HS.QuasiQuote{} k = unsupported "template haskell"
cpsExp HS.TypeApp{}    k = unsupported "type application"
cpsExp HS.XTag{}       k = unsupported "XML expression"
cpsExp HS.XETag{}      k = unsupported "XML expression"
cpsExp HS.XPcdata{}    k = unsupported "XML expression"
cpsExp HS.XExpTag{}    k = unsupported "XML expression"
cpsExp HS.XChildTag{}  k = unsupported "XML expression"
cpsExp HS.CorePragma{} k = unsupported "pragma during CPS"
cpsExp HS.SCCPragma{}  k = unsupported "pragma during CPS"
cpsExp HS.GenPragma{}  k = unsupported "pragma during CPS"
cpsExp HS.Proc{}            k = unsupported "arrow syntax"
cpsExp HS.LeftArrApp{}      k = unsupported "arrow syntax"
cpsExp HS.RightArrApp{}     k = unsupported "arrow syntax"
cpsExp HS.LeftArrHighApp{}  k = unsupported "arrow syntax"
cpsExp HS.RightArrHighApp{} k = unsupported "arrow syntax"
-- looks like we have an outdated haskell-src-exts that predates this
-- cpsExp HS.ArrOp{}           k = unsupported "arrow syntax"
cpsExp HS.LCase{} k = unsupported "lambda case"

-- | CPS an alternative in a 'case' statement.
cpsAlt :: HS.Alt ann -> CpsCont -> CPSM (CpsPat, CpsExp)
-- we should be able to support this by just wrapping the cps'd RHS in
-- a 'let binds in rhs'-style expression. Guards cause the RHS to turn
-- into a case statement so putting let bindings before that should work.
cpsAlt (HS.Alt _ _ _ (Just binds)) k = unsupported "'where' in case alternative"
cpsAlt (HS.Alt _ pat rhs Nothing)  k = (asCpsPat pat,) <$> cpsRhs rhs k

-- | CPS the RHS of a decl or 'case' alternative.
-- BREAKS SEMANTICS: treats guards as a nested pattern match
--   whereas a join point would be needed in practice. But we
--   don't care about the behavior of fall-through here.
cpsRhs :: HS.Rhs ann -> CpsCont -> CPSM CpsExp
cpsRhs (HS.UnGuardedRhs _ e) k = cpsExp e k
-- idea: evaluate all of the guards, then MatchCps AConst
-- with one constant pattern for each of possible branches.
cpsRhs (HS.GuardedRhss _ grhss) k = do
    let (guardExps, rhsExps) = collectGrhss grhss
    cpsRhsExps <- mapM (\e -> cpsExp e k) rhsExps
    let cpsRhsClauses = map (ConstPat,) cpsRhsExps
    unused <- fresh "_"
    cpsMultiExp GuardMEC guardExps $ 
      FnCont unused $ MatchCps Const cpsRhsClauses

data MultiExpContext
  = TupleMEC
  | ListMEC
  | GuardMEC

instance Show MultiExpContext where
  show TupleMEC = "()"
  show ListMEC  = "[]"
  show GuardMEC = "|"

-- | CPS several expressions and effectively throw away the results
-- but guarantee that they still appear by applying them to either
-- '|', '[]', or '()' (none of which could be redefined by the code being
-- transformed) depending on what we're doing.
-- The application '() 1 2' is a proxy for '(1,2)'.
cpsMultiExp :: MultiExpContext -> [HS.Exp ann] -> CpsCont -> CPSM CpsExp
cpsMultiExp context es k = go [] es
  where
    go ses [] = do
      return $ AppCps (Var (show context)) (reverse ses) k
    go ses (e:es) = cpsValueM e "e" $ \se -> go (se:ses) es

-- | Collect an application tree into an application head
-- and a list of argument expressions. The arguments appear
-- from RIGHT TO LEFT. This is natural for a right-to-left
-- evaluation order.
collectApp :: HS.Exp ann -> (HS.Exp ann, [HS.Exp ann])
collectApp exp = go exp
  where go (HS.App _ left arg) = let (f, args) = go left
                                 in (f, arg : args)
        go (HS.Paren _ e) = go e
        
        go (HS.InfixApp _ l op r) = (HS.Var ann name, [r, l])
          where (ann, name) = case op of
                  HS.QVarOp ann name -> (ann, name)
                  HS.QConOp ann name -> (ann, name)

        go other = (other, [])

-- | Reconstruct a collected HS.App into an AppCps tree.
rebuildApp :: HS.Exp ann -> [HS.Exp ann] -> CpsCont -> CPSM CpsExp
rebuildApp head args k = go [] args
  where
    go seArgs []  = cpsValue head "f" $ \se -> AppCps se seArgs k
    go acc (x:xs) = cpsValueM x "e" $ \se -> go (se:acc) xs

-- | Collect a list of GuardedRhss into a list of guard
-- expressions and a list of RHS expressions.
collectGrhss :: [HS.GuardedRhs ann] -> ([HS.Exp ann], [HS.Exp ann])
collectGrhss [] = ([], [])
collectGrhss (HS.GuardedRhs _ stmts e : rest)
  | [HS.Qualifier _ g] <- stmts 
  = let (gs, rs) = collectGrhss rest
    in (g:gs, e:rs)

  | otherwise
  = unsupported "pattern guard"

-- Translate an HS.Pat to a CpsPat
asCpsPat :: HS.Pat ann -> CpsPat
asCpsPat (HS.PVar _ name) = VarPat $ flatName name
asCpsPat (HS.PLit _ _ _)  = ConstPat
asCpsPat HS.PNPlusK{} = unsupported "n+k pattern"
asCpsPat (HS.PInfixApp _ l op r) = 
  ConstrPat (flatName op) [asCpsPat l, asCpsPat r]
asCpsPat (HS.PApp _ name pats) = 
  ConstrPat (flatName name) $ map asCpsPat pats
asCpsPat (HS.PTuple _ HS.Boxed (p:ps)) = 
  TuplePat $ NE.map asCpsPat (p :| ps)
asCpsPat (HS.PTuple _ HS.Unboxed _) = unsupported "unboxed tuple"
asCpsPat (HS.PList _ pats) =
  ConstrPat "[]" $ map asCpsPat pats
asCpsPat (HS.PParen _ pat) = asCpsPat pat
asCpsPat HS.PRec{} = unsupported "record pattern"
asCpsPat (HS.PAsPat _ name pat) = AsPat (flatName name) (asCpsPat pat)
asCpsPat (HS.PWildCard _) = ConstPat
asCpsPat (HS.PIrrPat _ pat) = asCpsPat pat -- irrefutable patterns are a
                                           -- strictness thing; we really
                                           -- don't care here.
asCpsPat (HS.PatTypeSig _ pat _) = asCpsPat pat -- type shouldn't be able
                                                -- to refer to expression vars
asCpsPat HS.PViewPat{} = unsupported "view pattern"
asCpsPat HS.PRPat{}    = unsupported "HaRP pattern"
asCpsPat HS.PXTag{}    = unsupported "XML pattern"
asCpsPat HS.PXETag{}   = unsupported "XML pattern"
asCpsPat HS.PXPcdata{} = unsupported "XML pattern"
asCpsPat HS.PXPatTag{} = unsupported "XML pattern"
asCpsPat HS.PXRPats{}  = unsupported "XML pattern"
asCpsPat HS.PSplice{}  = unsupported "template haskell (pattern)"
asCpsPat HS.PQuasiQuote{} = unsupported "template haskell (pattern)"
asCpsPat (HS.PBangPat _ pat) = asCpsPat pat -- see PIrrPat

-------------------------------------------------------------------------------
-- Debugging
-------------------------------------------------------------------------------

-- Debugging; we don't need a whole pretty printer, just enough
-- to be able to read what's going on.
showWithContinuation :: CpsCont -> ShowS -> ShowS
showWithContinuation c@(VarCont _)  a = shows c . showString " $ " . a
showWithContinuation c@(FnCont _ _) a = a . showString " & " . shows c

instance Show SimpleExp where
  show Const = "AConst"
  show (Var name) = name
  show (Unq unique) = show unique

instance Show Unique where
  show (Unique n i) = n ++ "%" ++ show i

instance Show CpsPat where
  showsPrec _ ConstPat = showString "AConst"
  showsPrec _ (VarPat name) = showString name
  showsPrec _ (TuplePat pats) = showParen True $
    -- type is ShowS, so (.) ~ (++) and id ~ ""
    foldr (.) id $ NE.intersperse (showString ", ") $
      NE.map shows pats
  showsPrec _ (ConstrPat name []) = showString name
  showsPrec _ (ConstrPat name (p:ps)) = showString name
                                    . showChar ' '
                                    . shows (TuplePat (p:|ps))

instance Show ContVar where
  showsPrec _ (KVar i) = showString "_k" . shows i

instance Show CpsCont where
  showsPrec _ (VarCont cv) = shows cv
  showsPrec _ (FnCont name exp) = showString "FN " . shows name
                                . showString " -> " . shows exp

intercalateS :: String -> [ShowS] -> ShowS
intercalateS sep = go
  where go []     = id
        go [s]    = s
        go (s:ss) = s . showString sep . go ss

instance Show CpsExp where
  showsPrec _ (SimpleExpCps e k) = showWithContinuation k (shows e)
  showsPrec _ (BinOpAppCps l op r k) =
    showWithContinuation k $ intercalateS " " [shows l, showString op, shows r]
  showsPrec _ (MatchCps e clauses) = showString "case " . shows e 
    . showString " of { " . intercalateS "; " (map showClause clauses)
    . showString " }"
  -- I'm doing it this way for consistency but it would be more syntactically 
  -- appropriate to pass simple continuations directly to the function being 
  -- applied and to use '$' for complex continuations.
  showsPrec _ (AppCps head args k) = showWithContinuation k $
    shows head . showChar ' ' . intercalateS " " (map shows args)
  showsPrec _ (LamCps pat kv e k) = showWithContinuation k $
    showParen True $ showChar '\\' . shows pat . showChar ' '
    . shows kv . showString " -> " . shows e

showClause :: (CpsPat, CpsExp) -> ShowS
showClause (p, e) = shows p . showString " -> " . shows e
