{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use infix" #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module CallGraph where
import CPS
import Data.List
import TailRecursion

------------
-- GRAPHS --
------------

-- | A global identifier for a function in the call graph. 
-- A function `f` defined inside `g` defined inside `h` is represented as a
-- list [f,g,h].
newtype Vertex = Vertex [Binder]
  deriving (Eq)

-- | Call graphs are represented as lists of vertices and directed edges.
data CallGraph = CallGraph {
  vertices :: [Vertex],
  calls :: [(Vertex, Vertex)],
  tailCalls :: [(Vertex, Vertex)]
}
  deriving (Eq)

instance Show Vertex where
  show (Vertex [x]) = show x
  show (Vertex (x:xs)) = show x ++ "." ++ show (Vertex xs)

instance Show CallGraph where
  show (CallGraph vertices calls tailCalls) =
    "Vertices: " ++ show vertices ++ "\n" ++
    "Edges:\n\t" ++ intercalate "\n\t" arrows
    where
      arrow1 (v1, v2) = show v1 ++ " -call-> " ++ show v2
      arrow2 (v1, v2) = show v1 ++ " -tail-> " ++ show v2
      arrows = map arrow1 calls ++ map arrow2 tailCalls

emptyGraph :: CallGraph
emptyGraph = CallGraph [] [] []

addVertex :: Vertex -> CallGraph -> CallGraph
addVertex v (CallGraph vs es1 es2) = CallGraph (v:vs) es1 es2

addCall :: (Vertex, Vertex) -> CallGraph -> CallGraph
addCall e@(v1, v2) (CallGraph vs es1 es2) = CallGraph (union [v1,v2] vs) (e:es1) es2

addTailCall :: (Vertex, Vertex) -> CallGraph -> CallGraph
addTailCall e@(v1, v2) (CallGraph vs es1 es2) = CallGraph (union [v1,v2] vs) es1 (e:es2)

mergeGraphs :: CallGraph -> CallGraph -> CallGraph
mergeGraphs g1 g2 = CallGraph (vertices g1 `union` vertices g2) (calls g1 `union` calls g2) (tailCalls g1 `union` tailCalls g2)

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

  AppCps (Var f) _ k ->
    if isTailCall
      then addTailCall (caller, callee) subgraph
      else addCall (caller, callee) subgraph
    where caller = parent ctx
          callee = lookupID ctx f
          subgraph = buildGraphFromCont ctx k
          isTailCall = case k of VarCont {} -> True; FnCont {} -> False

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


----
-- Checker
----

-- | As we do DFS on the call graph, the breadcrumbs keeps track of the vertices
-- and edges we've already seen. A trail [(v1, true), (v2, false)] indicates
-- that (1) v1 called v2 tail recursively, and (2) v2 called us not-tail-recursively.
type BreadCrumbs = [(Vertex, Bool)]

contains :: BreadCrumbs -> Vertex -> Bool
contains crumbs v = any ((==) v . fst) crumbs

-- | Assuming there is a cycle, i.e. crumbs `contains` v, check whether the
-- cycle contains any non-tail calls.
diagnoseCycle :: BreadCrumbs -> Vertex -> Bool -> Truth
diagnoseCycle crumbs v isTailCall =
  -- If v is not being called tail recursively, then clearly we have 
  -- a non-tail-recursive cycle!
  if not isTailCall then Fails else
  -- Otherwise, check whether any of the calls from v were non-tail-calls.
  let suffix = dropWhile ((/=) v . fst) crumbs
      anyBadCalls = any ((==) False . snd) suffix
  in
  if anyBadCalls then Fails else Holds


-- | Checks whether the given function is tail recursive in the call graph.
-- If the function cannot reach any cycles, return `Vacuous` (not recursive).
-- If the function can reach a cycle, but the cycle contains a non-tail call,
-- then return `Fails` (because it uses non-tail recursion).
-- Otherwise, return `Holds`.
isTailRecursive :: Name -> CallGraph -> Truth
isTailRecursive root graph = go [] (Vertex [BindRaw root]) graph
  where
    go :: BreadCrumbs -> Vertex -> CallGraph -> Truth
    go crumbs vertex graph =
      let
        -- Find all edges from `vertex`; "good" edges are tail calls, "bad"
        -- edges are non-tail-calls.
        goodEdges = filter ((==) vertex . fst) (tailCalls graph)
        badEdges  = filter ((==) vertex . fst) (calls graph)

        -- Check all the outgoing edges.
        results1 = map (recur True . snd) goodEdges
        results2 = map (recur False . snd) badEdges

        -- Process an edge from `vertex` to `nextVertex`. If `nextVertex` occurs
        -- in the breadcrumbs, then we have a cycle; check whether it has bad
        -- edges. Otherwise, recurse for that vertex, seeing if there are any
        -- good or bad cycles in that subtree.
        recur isTailCall nextVertex =
          if crumbs `contains` nextVertex then
            diagnoseCycle crumbs nextVertex isTailCall
          else
            go (crumbs ++ [(vertex, isTailCall)]) nextVertex graph
      in
        -- Combine all the results of the different branches.
        mconcat results1 <> mconcat results2