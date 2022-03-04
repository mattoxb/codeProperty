module CallGraph where
import CPS
import Data.List
import TailRecursion

{-

Let $f$ be the function we are checking for tail recursion.

We need to distinguish the following common situations: 
1.  $f$ can make non-tail calls to a helper function $g$ as long as $g$ does not
recurse back to $f$. If $g$ does recurse back to $f$, then $f$ fails the check.
2. $f$ can tail-recursively call an "aux" function $g$, as long as $g$ is tail
recursive itself. If $g$ is bad-recursive, then $f$ fails the check.

```haskell
-- good, even though f makes a non-tail call
helper n = n - 1 f n = if n < 0 then n else f (helper n)

-- good, the helper function is tail recursive
f n = aux n 1 where aux n acc = if n == 0 then acc else aux (n - 1) (n * acc)

-- bad, the helper function is not tail recursive
f n = aux n where aux n = if n == 0 then 1 else n * aux (n - 1) 
```

Hence we should inspect the entire program call graph in order to decide whether
$f$ is tail recursive.

# Definitions

$f \to_1 g$ denotes "$f$ makes a non-tail call to $g$".  $f \to_2 g$ denotes
"$f$ makes a tail call to $g$".  $f \to g$ denotes "$f$ makes some sort of call
to $g$".

We say $f$ **can reach** $g$ if $f \to^* g$.

Let $G$ be the call graph, where edges are labelled with 1 or 2, according to
the notation above.

If $C$ is a strongly connected component and one of the edges is a non-tail
call, then $C$ is a **bad component**. Otherwise, $C$ is a **good component**.

$f$ **fails** if it can reach a bad component. $f$ **passes** if it can reach a
good component and can't reach any bad components.

A module passes the check if the desired function passes, and all other
functions don't fail.

# Algorithm

1. Compute the SCCs of $G$ 2. Mark each SCC as either bad or good 3. If $f$ can
reach a bad component, then $f$ **fails**. Otherwise, if $f$ can reach a
nontrivial (size > 1) component, then $f$ **passes**. Otherwise, $f$ is vacuous.
-}

------------
-- GRAPHS --
------------

-- | A global identifier for a function in the call graph. 
-- A function `f` defined inside `g` defined inside `h` is represented as a
-- list [f,g,h].
newtype Vertex = Vertex [Binder]
  deriving Eq

-- | Call graphs are represented as lists of vertices and directed edges.
-- There are two kinds of directed edges: "tailCalls" and non-tail "calls".
data CallGraph = CallGraph {
  vertices :: [Vertex],
  calls :: [(Vertex, Vertex)],
  tailCalls :: [(Vertex, Vertex)]
}

instance Show Vertex where
  show (Vertex [])  = error "Undefined vertex in call graph"
  show (Vertex [x]) = show x
  show (Vertex (x:xs)) = show (Vertex xs) ++ "." ++ show x

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
addCall e@(v1, v2) (CallGraph vs es1 es2) = CallGraph ([v1,v2] `union` vs) (e:es1) es2

addTailCall :: (Vertex, Vertex) -> CallGraph -> CallGraph
addTailCall e@(v1, v2) (CallGraph vs es1 es2) = CallGraph ([v1,v2] `union` vs) es1 (e:es2)

mergeGraphs :: CallGraph -> CallGraph -> CallGraph
mergeGraphs g1 g2 = CallGraph (vertices g1 `union` vertices g2) (calls g1 `union` calls g2) (tailCalls g1 `union` tailCalls g2)

merge :: [CallGraph] -> CallGraph
merge = foldr mergeGraphs emptyGraph

--------------
-- BUILDING --
--------------

-- | As we traverse the CPS module, we need to know all the binders enclosing
-- the expression and maintain a mapping from binders to their unique
-- identifier. We also maintain "path", the sequence of enclosing binders,
-- in order to build unique identifiers.
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
- If looking at an App expression:
  - The closest enclosing function is the caller.
  - The vertex of the called function is the callee.
  - If the function is called with a `VarCont` continuation, then it's 
    a tail call. (This is because in our CPS transform, the `VarCont`
    is guaranteed to be the continuation parameter of the enclosing
    function.) Otherwise, if the function is being called with `FnCont`,
    then it is definitely not a tail call. (This is because the function
    is being called with a different continuation.)
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

  -- XXX What does it mean when we apply a continuation to a lambda?
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