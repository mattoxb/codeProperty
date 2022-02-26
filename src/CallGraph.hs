{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use infix" #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module CallGraph where
import CPS
import Data.List

------------
-- GRAPHS --
------------

-- | A global identifier for a function in the call graph. 
-- A function `f` defined inside `g` defined inside `h` is represented as a
-- list [f,g,h].
newtype Vertex = Vertex [Binder]
  deriving (Eq)

-- | Call graphs are represented as lists of vertices and directed edges.
data CallGraph = CallGraph { vertices :: [Vertex], edges :: [(Vertex, Vertex)] }
  deriving (Eq)

instance Show Vertex where
  show (Vertex [x]) = show x
  show (Vertex (x:xs)) = show x ++ "." ++ show (Vertex xs)

instance Show CallGraph where
  show (CallGraph vertices edges) =
    "Vertices: " ++ show vertices ++ "\n" ++
    "Edges:\n\t" ++ intercalate "\n\t" arrows
    where
      arrow (v1, v2) = show v1 ++ " -> " ++ show v2
      arrows = map arrow edges

emptyGraph :: CallGraph
emptyGraph = CallGraph [] []

addVertex :: Vertex -> CallGraph -> CallGraph
addVertex v (CallGraph vs es) = CallGraph (v:vs) es

addEdge :: (Vertex, Vertex) -> CallGraph -> CallGraph
addEdge e@(v1, v2) (CallGraph vs es) = CallGraph (union [v1,v2] vs) (e:es)

mergeGraphs :: CallGraph -> CallGraph -> CallGraph
mergeGraphs g1 g2 = CallGraph (vertices g1 `union` vertices g2) (edges g1 `union` edges g2)

merge :: [CallGraph] -> CallGraph
merge = foldr mergeGraphs emptyGraph

--------------
-- BUILDING --
--------------

-- | As we recurse, we need to know the path of binders enclosing the expression
-- and a mapping from binders to their unique identifier.
data Context = Context { path :: [Binder], scope :: [(Binder, Vertex)] }
  deriving (Show, Eq)

emptyContext :: Context
emptyContext = Context [] []

parent :: Context -> Vertex
parent = Vertex . path

updateScope :: [(Binder, Vertex)] -> Context -> Context
updateScope sc (Context p sc') = Context p (sc ++ sc')

withParent :: Binder -> Context -> Context
withParent bnd (Context p sc) = Context (bnd : p) sc

lookupID :: Context -> Binder -> Vertex
lookupID ctx bndr = case lookup bndr (scope ctx) of
  Just v -> v
  Nothing -> Vertex [bndr]

{-
For each expression:
- Create a vertex in the call graph for each top-level definition, each
  let-bound variable, and each parameter.
- Take note of the binding in which each expression is defined.
- Take note of the continuation associated with the binding.
- If looking at an App expression:
  - The closest enclosing function is the caller.
  - The vertex of the called function is the callee.
  - If the function is called with the same continuation as the caller's
    parameter, it's a tail call. Otherwise, it's not.
-}

buildGraph :: Context -> [CpsBinding] -> (CallGraph, Context)
buildGraph ctx bindings =
  let binders   = map (\(Binding bnd _ _) -> bnd) bindings
      exps      = map (\(Binding _ _ exp) -> exp) bindings
      vertices  = map (toVertex ctx) binders
      ctx'      = updateScope (zip binders vertices) ctx
      subgraphs = map buildSubgraph bindings
      buildSubgraph (Binding f _ exp) =
        buildGraphFromExp (withParent f ctx') exp
  in (merge subgraphs, ctx')

buildGraphFromExp :: Context -> CpsExp -> CallGraph
buildGraphFromExp ctx exp = case exp of

  SimpleExpCps _ k -> buildGraphFromCont ctx k

  MatchCps _ clauses -> merge subgraphs
    where subgraphs = map subgraphOf clauses
          subgraphOf (pat, exp) =
            let ctx' = updateScope (toScope ctx pat) ctx
            in buildGraphFromExp ctx' exp

  AppCps (Var f) _ k -> addEdge (caller, callee) subgraph
    where caller = parent ctx
          callee = lookupID ctx f
          subgraph = buildGraphFromCont ctx k

  -- I *think* that applying a constant means that the code doesn't compile.
  -- Let's just ignore it.
  AppCps Const _ k -> buildGraphFromCont ctx k

  LamCps pat cv exp k -> merge [kGraph, eGraph]
    where
      ctx' = updateScope (toScope ctx pat) ctx
      kGraph = buildGraphFromCont ctx' k
      eGraph = buildGraphFromExp ctx' exp

  LetCps bindings exp -> merge [expGraph, bindingGraph]
    where (bindingGraph, ctx') = buildGraph ctx bindings
          expGraph = buildGraphFromExp ctx' exp

buildGraphFromCont :: Context -> CpsCont -> CallGraph
buildGraphFromCont ctx cont = case cont of
  VarCont cv -> emptyGraph
  FnCont un ce ->
    let x = BindUnq un
        ctx' = updateScope [(x, toVertex ctx x)] ctx
    in buildGraphFromExp ctx' ce

toVertex :: Context -> Binder -> Vertex
toVertex ctx x = Vertex (x : path ctx)

toScope :: Context -> CpsPat -> [(Binder, Vertex)]
toScope ctx pat =
  case pat of
  ConstPat -> []
  VarPat x -> [(x, toVertex ctx x)]
  AsPat  x pat -> (x, toVertex ctx x) : toScope ctx pat
  TuplePat pats -> concatMap (toScope ctx) pats
  ConstrPat _ pats -> concatMap (toScope ctx) pats


-- 
-- INTERFACE
--

