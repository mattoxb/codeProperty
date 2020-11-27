{-# LANGUAGE TupleSections      #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# Language LambdaCase         #-}

module CPS where

import Errors (unsupported)
import HSEExtra (HasName(flatName))

import           Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import Data.Data (Data, Typeable)
import Data.Maybe (catMaybes)

import Control.Monad.State.Strict
    (evalState, MonadState(state), State)
import Control.Lens (transformM, Plated, toListOf, (%~))
import Data.Data.Lens (biplate)

import qualified Language.Haskell.Exts as HS

type Name = String
type Op   = Name

-- | a fresh name generated during CPS or tail recursion
-- detection. Differentiating between these and source Vars
-- is not strictly necessary but makes renaming much easier,
-- allowing us to worry less while detecting tail recursion.
data Unique = Unique Provenance Name !Int
  deriving (Eq, Typeable, Data)

data Provenance
  = CpsTransform
  | Renaming
  deriving (Eq, Typeable, Data)

data Binder
  = BindRaw Name -- ^ raw binding; perhaps a free var (global)
                 --  or just has not yet been renamed
  | BindUnq !Unique
  deriving (Eq, Typeable, Data)

-- | A Simple Expression in CPS.
-- Variable names are preserved to detect alpha-capture later.
-- If a value is a constant, we really don't care what it is.
data SimpleExp
  = Const
  | Var Binder
  deriving (Eq, Typeable, Data)

mkRawVar :: Name -> SimpleExp
mkRawVar = Var . BindRaw

mkUnqVar :: Unique -> SimpleExp
mkUnqVar = Var . BindUnq

-- We don't care about the transform being exactly correct in terms
-- of the shapes of patterns (esp. w.r.t to how functions are actually
-- applied) because we're never going to run the code. But we _do_ need
-- to know the names of the binders in lambdas. Thus it's OK to, for
-- example, translate [1, 2, x] as
-- ConstrPat "[]" [ConstPat, ConstPat, VarPat "x"].
data CpsPat
  = ConstPat -- we don't really care about constant values
             -- wildcard pattern is a ConstPat too
  | VarPat Binder
  | AsPat  Binder CpsPat
  | TuplePat (NonEmpty CpsPat) -- in fact there are always >= 2
  | ConstrPat Name [CpsPat] -- constructor name is needed?
    -- pattern "()" needs to be translated as ConstrPat "()" []
    -- Note that we use Name and not Binder because the constructor's
    -- name is not being bound!
  deriving (Eq, Typeable, Data)

newtype ContVar = KVar Int -- distinguishing is convenient for debugging
                        -- but not actually necessary since there's
                        -- no non-local continuations in Haskell
  deriving (Eq, Typeable, Data)

data CpsCont
  = VarCont ContVar
  | FnCont Unique CpsExp
  deriving (Eq, Typeable, Data)

data CpsExp
  = SimpleExpCps SimpleExp CpsCont
  | MatchCps SimpleExp [Clause]
  | AppCps SimpleExp [SimpleExp] CpsCont
  | LamCps CpsPat ContVar CpsExp CpsCont
  | LetCps [CpsBinding] CpsExp
  deriving (Eq, Typeable, Data)

instance Plated CpsExp

type Clause = (CpsPat, CpsExp)

{- | A Decl but in CPS. We use some hacks here to accomplish our goals:
(1) All Haskell Decls get converted into a name binding an expression in
    the following way:
      foo x 0 = bar x where ...1
      foo x 1 = baz x where ...2
    becomes
      foo k = case Const of
        { (x, Const) -> let ...1 in [[bar x]]_k
        ; (x, Const) -> let ...2 in [[baz x]]_k
        }
    Guards are handled the same way as for case expressions.
(2) This includes simple pattern bindings (which may be eta-reduced function
    bindings, otherwise we would just ignored them), so that
      foo = go 0 where ...
    becomes
      foo k = let ... in [[go 0]]_k
(3) non-simple pattern bindings, like (a, b) = (useX1, useX2) where X = ...
    are not allowed.

Note that the first 2 points are a major CPS semantics break; the result is
not actually a function! However it is sufficient for our needs, which are
to make the order of evaluation in the body explicit.
-}
data CpsBinding = Binding Binder ContVar CpsExp
  deriving (Eq, Typeable, Data)

binderOfBinding :: CpsBinding -> Binder
binderOfBinding (Binding bndr _ _) = bndr

-------------------------------------------------------------------------------
-- CPS Transform
-------------------------------------------------------------------------------

fresh :: Provenance -> Name -> State Int Unique
fresh prov pre = Unique prov pre <$> next

type CPSM = State Int

freshCPS :: Name -> CPSM Unique
freshCPS = fresh CpsTransform

runCPSMFrom :: Int -> CPSM a -> a
runCPSMFrom = flip evalState

runCPSM :: CPSM a -> a
runCPSM = runCPSMFrom 0

next :: CPSM Int
next = state $ \s -> (s, s+1)

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
-- Variable names are preserved (as raw vars), but values of constants
-- are not. See 'SimpleExp'.
asSimpleExp :: HS.Exp ann -> SimpleExp
asSimpleExp (HS.Var _ name) = mkRawVar $ flatName name
-- We maybe don't need to keep these names around at all?
asSimpleExp (HS.Con _ name) = mkRawVar $ flatName name
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
  | otherwise  = do v <- freshCPS pre
                    contBody <- consumer (mkUnqVar v)
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
      return $ AppCps (Var (BindRaw name)) [v1,v2] k
  where name = flatName bigName

cpsExp app@HS.App{} k = rebuildApp head args k
  where (head, args) = collectApp app

cpsExp (HS.NegApp _ e) k = cpsValue e "v" $ \se ->
  AppCps (mkRawVar "Prelude.negate") [se] k

cpsExp (HS.Lambda _ pats body) k = do
  kvar <- freshKVar
  -- we don't care about how many syntactic arguments the lambda has,
  -- but we do care about what names are present in their patterns
  let cpsPat = asCpsPat $ HS.PTuple undefined HS.Boxed pats
  cpsBody <- cpsExp body $ VarCont kvar
  return $ LamCps cpsPat kvar cpsBody k

cpsExp (HS.Let _ (HS.BDecls _ decls) body) k = do
  cpsBinds <- cpsBindings decls
  cpsBody  <- cpsExp body k
  return $ LetCps cpsBinds cpsBody
cpsExp (HS.Let _ HS.IPBinds{} _) k = unsupported "implicit parameter binding"

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
-- but honestly, who writes '(1+) 2' in real code?
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
cpsExp HS.ArrOp{}           k = unsupported "arrow syntax"
cpsExp HS.LCase{} k = unsupported "lambda case"
-- These last 3 are to shut up the pattern match exhaustiveness warning.
cpsExp HS.Var{} k = error "cpsExp: isSimple missed a Var!"
cpsExp HS.Con{} k = error "cpsExp: isSimple missed a Con!"
cpsExp HS.Lit{} k = error "cpsExp: isSimple missed a Lit!"

-- | CPS an alternative in a 'case' statement.
cpsAlt :: HS.Alt ann -> CpsCont -> CPSM (CpsPat, CpsExp)
cpsAlt (HS.Alt _ pat rhs mbinds) k =
  (asCpsPat pat,) <$> cpsRhsWithLocals mbinds rhs k

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
    unused <- freshCPS "_"
    cpsMultiExp GuardMEC guardExps $
      FnCont unused $ MatchCps Const cpsRhsClauses

-- | 'cpsRhs', but wraps the rhs in a let expression if there are bindings.
-- If the 'rhs' has guards, the guards are CPS'd as a case statement, and the
-- case statement will end up in the body of the let-expression, which
-- handles scope correctly.
cpsRhsWithLocals :: Maybe (HS.Binds ann)
                 -> HS.Rhs ann 
                 -> CpsCont 
                 -> CPSM CpsExp
cpsRhsWithLocals Nothing rhs k = cpsRhs rhs k
cpsRhsWithLocals (Just (HS.BDecls _ decls)) rhs k = do
  binds <- cpsBindings decls
  case binds of
    [] -> cpsRhs rhs k
    bs -> LetCps bs <$> cpsRhs rhs k
cpsRhsWithLocals (Just HS.IPBinds{}) rhs k = 
  unsupported "implicit parameter binding"

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
    go ses [] =
      return $ AppCps (mkRawVar (show context)) (reverse ses) k
    go ses (e:es) = cpsValueM e "e" $ \se -> go (se:ses) es

-- | Collect an application tree into an application head
-- and a list of argument expressions. The arguments appear
-- from RIGHT TO LEFT. This is natural for a right-to-left
-- evaluation order.
collectApp :: HS.Exp ann -> (HS.Exp ann, [HS.Exp ann])
collectApp = go
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
    go acc (x:xs) = cpsValueM x "a" $ \se -> go (se:acc) xs

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

-- | CPS a Haskell binding, top-level or otherwise.
-- See the note on 'CpsBinding'.
cpsBinding :: HS.Decl ann -> CPSM (Maybe CpsBinding)
cpsBinding (HS.FunBind ann ms@(HS.Match _ hsname _ _ _ : _)) = do
  let name = flatName hsname
      alts = map matchAsAlt ms
      explode = error "cpsBinding: annotation in synthetic case was forced"
      anyConstant = HS.Int explode 0 "0"
      caseExp = HS.Case ann (HS.Lit explode anyConstant) alts
  kvar <- freshKVar
  body <- cpsExp caseExp (VarCont kvar)
  return $ Just $ Binding (BindRaw name) kvar body
cpsBinding (HS.PatBind _ (HS.PVar _ name) rhs mbinds) = 
  do cont <- freshKVar
     exp  <- cpsRhsWithLocals mbinds rhs $ VarCont cont
     return $
       Just $
       Binding (BindRaw $ flatName name) cont exp

-- matches if the pat is not a PVar
cpsBinding HS.PatBind{} = unsupported "pattern binding"
-- matches if the list of HS.Matches is empty
cpsBinding HS.FunBind{} = error "cpsBinding: function decl with no clauses"
cpsBinding _ = pure Nothing

-- | CPS all of the FunBinds and PatBinds in a list of Decls. Everything
-- else is thrown away.
cpsBindings :: [HS.Decl ann] -> CPSM [CpsBinding]
cpsBindings = fmap catMaybes . mapM cpsBinding

-- | Convert a Match to an Alt
-- More or less just throws away the normal/infix distinction
matchAsAlt :: HS.Match ann -> HS.Alt ann
matchAsAlt match = HS.Alt ann pat rhs mbinds
  where HS.Match ann _ pats rhs mbinds = unInfix match

        unInfix m@HS.Match{} = m
        unInfix (HS.InfixMatch ann lpat n rpats rhs mbinds) =
          HS.Match ann n (lpat:rpats) rhs mbinds

        pat = HS.PTuple undefined HS.Boxed pats

-- Translate an HS.Pat to a CpsPat
asCpsPat :: HS.Pat ann -> CpsPat
asCpsPat (HS.PVar _ name) = VarPat $ BindRaw $ flatName name
asCpsPat HS.PLit{} = ConstPat
asCpsPat HS.PNPlusK{} = unsupported "n+k pattern"
asCpsPat (HS.PInfixApp _ l op r) =
  ConstrPat (flatName op) [asCpsPat l, asCpsPat r]
asCpsPat (HS.PApp _ name pats) =
  ConstrPat (flatName name) $ map asCpsPat pats
asCpsPat (HS.PTuple _ _ []) = -- this should be impossible
  error "asCpsPat: empty tuple from haskell-src-exts"
asCpsPat (HS.PTuple _ HS.Boxed (p:ps)) =
  TuplePat $ NE.map asCpsPat (p :| ps)
asCpsPat (HS.PTuple _ HS.Unboxed _) = unsupported "unboxed tuple"
asCpsPat HS.PUnboxedSum{} = unsupported "unboxed sum"
asCpsPat (HS.PList _ pats) =
  ConstrPat "[]" $ map asCpsPat pats
asCpsPat (HS.PParen _ pat) = asCpsPat pat
asCpsPat HS.PRec{} = unsupported "record pattern"
asCpsPat (HS.PAsPat _ name pat) =
  AsPat (BindRaw $ flatName name) (asCpsPat pat)
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

{------------------------------------------------------------------------------
-- Renaming

This section is for the renaming of subexpressions in a CpsExp tree. The idea
is that _any_ name bound locally (i.e. not globally) gets replaced by a Unique
at its binding site and everywhere it is used.
------------------------------------------------------------------------------}

-- | "Renamer"
-- (this is a common abbreviation in compilers)
type Rn = State Int

runRn :: Rn a -> a
runRn = flip evalState 0

freshRn :: Name -> Rn Unique
freshRn = fresh Renaming

-- | Rename all bound variables in a Binding. This results in renaming the
-- arguments of the binding, if it had any, but not the binding itself.
-- Intended for global bindings; local bindings are handled by a call to
-- 'renameThingMany' in 'renameSubexp'.
renameBinding :: CpsBinding -> Rn CpsBinding
renameBinding (Binding bndr k body) = Binding bndr k <$> renameExp body

-- | Rename all bound variables in an entire CpsExp to disambiguate them.
-- In the resulting CpsExp, the only raw binders are free variables of the
-- input.
renameExp :: CpsExp -> Rn CpsExp
-- transformM works bottom-up, which correctly handles shadowing naturally!
renameExp = transformM renameSubexp

-- | Replace all instances of the given raw name in binders with
-- the given unique.
renameThingOnce :: Data thing
                => Name    -- ^ The name to replace
                -> Unique  -- ^ The Unique to replace it with
                -> thing   -- ^ Thing to rename in
                -> thing   -- ^ Renamed thing
renameThingOnce name unq = biplate %~ \case
  BindRaw name' | name == name' -> BindUnq unq
  otherBinder                   -> otherBinder

-- | Replace all instances of each raw name in the input with the
-- corresponding unique.
renameThingMany :: Data thing => [(Name, Unique)] -> thing -> thing
renameThingMany pairs thing = foldr (uncurry renameThingOnce) thing pairs

-- | Rename a CPS Subexpression by inspecting the root node only.
-- If the root node binds any names, fresh uniques are generated for them
-- and the entire scope of each binding is renamed with its unique,
-- including the binding site itself.
renameSubexp :: CpsExp -> Rn CpsExp
renameSubexp exp = case exp of
    SimpleExpCps{} -> pure exp
    MatchCps se clauses  -> MatchCps se <$> mapM renameClause clauses
    AppCps{}             -> pure exp
    LamCps pat var body k -> do
      pairs <- renamesForPat pat
      let rpat  = renameThingMany pairs pat  -- thing ~ CpsPat
          rbody = renameThingMany pairs body -- thing ~ CpsExp
      -- don't rename the continuation, because the binders don't
      -- scope over it!
      return $ LamCps rpat var rbody k
    LetCps binds body -> do
      let nameOfBind (Binding name _ _) = name
          boundNames = map nameOfBind binds
      renamePairs <- mapM (toSndM freshRn) $ catRaws boundNames
      -- This time, we rename ALL of the binders, their bodies,
      -- AND the body of the let itself. Haskell let-bindings
      -- are recursive!
      return $ renameThingMany renamePairs exp -- thing ~ CpsExp

-- | 'renameSubExp' for clauses.
renameClause :: Clause -> Rn Clause
renameClause clause@(pat,_) = do
  pairs <- renamesForPat pat
  return $ renameThingMany pairs clause -- thing ~ Clause

-- | Another "exactly what it says on the tin" function.
bindersInPat :: CpsPat -> [Binder]
bindersInPat = toListOf biplate

-- | 'bindersInPat', but only the raw binders.
rawBindersInPat :: CpsPat -> [Name]
rawBindersInPat = catRaws . bindersInPat

catRaws :: [Binder] -> [Name]
catRaws [] = []
catRaws (BindRaw name : rest) = name : catRaws rest
catRaws (BindUnq _    : rest) = catRaws rest

-- | For each raw binder in the pattern, generate a fresh unique.
renamesForPat :: CpsPat -> Rn [(Name, Unique)]
renamesForPat = mapM (toSndM freshRn) . rawBindersInPat

toSndM :: Functor m => (a -> m b) -> a -> m (a, b)
toSndM f a = (a,) <$> f a

-------------------------------------------------------------------------------
-- Debugging
-------------------------------------------------------------------------------

-- Debugging; we don't need a whole pretty printer, just enough
-- to be able to read what's going on.

instance Show SimpleExp where
  show Const = "AConst"
  show (Var binder) = show binder

instance Show Binder where
  show (BindRaw name) = name
  show (BindUnq unq)  = show unq

instance Show Unique where
  show (Unique p n i) = n ++ "%" ++ prov ++ show i
    where prov = case p of
            CpsTransform -> "cps"
            Renaming     -> "rn"

instance Show CpsPat where
  showsPrec _ ConstPat = showString "AConst"
  showsPrec _ (VarPat name) = shows name
  showsPrec _ (AsPat bndr pat) = shows bndr
                               . showChar '@'
                               . showParen True (shows pat)
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

showWithContinuation :: CpsCont -> ShowS -> ShowS
showWithContinuation c@(VarCont _)  a = shows c . showString " $ " . a
showWithContinuation c@(FnCont _ _) a = a . showString " & " . shows c

instance Show CpsExp where
  showsPrec _ (SimpleExpCps e k) = showWithContinuation k (shows e)
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
  showsPrec _ (LetCps binds body) = 
      showString "let { "
    . intercalateS "; " (map shows binds)
    . showString " } in " . shows body

instance Show CpsBinding where
  showsPrec _ (Binding name kvar exp) =
    shows name . showChar ' ' . shows kvar
    . showString " = " . shows exp

showClause :: (CpsPat, CpsExp) -> ShowS
showClause (p, e) = shows p . showString " -> " . shows e
