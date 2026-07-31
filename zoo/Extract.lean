/-
Zoo extractor for the `Neighborhood` library.

Scans the environment for theorems whose statement has the form `L₁ ⊂ L₂`,
`L₁ ⊆ L₂` or `L₁ = L₂` where `L₁ L₂ : Logic _` (i.e. `Set (Formula _)`),
reduces the collected inclusion graph by transitivity, and writes the
remaining edges to `zoo/neighborhood.json`.

Run from the repository root:

    lake env lean zoo/Extract.lean
-/
import Lean
import Neighborhood

open Lean Meta

namespace Zoo

inductive EdgeType
  | ssub
  | sub
  | eq
deriving BEq, Hashable, Repr

instance : ToString EdgeType := ⟨fun | .ssub => "ssub" | .sub => "sub" | .eq => "eq"⟩

/-- Composition of inclusions along a path: strict wins, equality is neutral. -/
def EdgeType.comp : EdgeType → EdgeType → EdgeType
  | .eq,  t    => t
  | t,    .eq  => t
  | .sub, .sub => .sub
  | _,    _    => .ssub

structure Edge where
  a : String
  b : String
  t : EdgeType
deriving BEq, Hashable, Repr

/-- A side of an inclusion names a concrete logic when its only free variables
are type variables (such as the atom type `α`); a side with a set-valued free
variable (e.g. `Hilbert Ax₁` in a generic monotonicity lemma) does not. -/
def isConcreteSide (xs : Array Expr) (e : Expr) : MetaM Bool := do
  let mut ok := true
  for x in xs do
    if e.containsFVar x.fvarId! then
      unless (← whnfR (← x.fvarId!.getType)).isSort do
        ok := false
  return ok

/-- Head constant of the conclusion of a (possibly universally quantified)
statement, read off syntactically without entering `MetaM`. -/
def conclusionHead : Expr → Name
  | .forallE _ _ b _ => conclusionHead b
  | e => e.getAppFn.constName

/-- Match a statement of the form `L₁ ⊂ L₂`, `L₁ ⊆ L₂` or `L₁ = L₂` with `L₁ L₂ : Logic _`
(possibly under universally quantified binders), returning the pretty-printed
pair `(L₁, L₂)` tagged with the kind of inclusion.

Note that the binders must be stripped with a non-reducing `forallTelescope`:
`⊆` on `Set` reducibly unfolds to `∀ a, a ∈ s → a ∈ t`, so the reducing
variant would telescope right through the statement we are looking for. -/
def matchInclusion (ci : ConstantInfo) : MetaM (Option Edge) := do
  forallTelescope ci.type fun xs body => do
    let (t, carrier, a, b) : EdgeType × Expr × Expr × Expr ←
      if body.isAppOfArity ``HasSSubset.SSubset 4 then
        pure (.ssub, body.getArg! 0, body.getArg! 2, body.getArg! 3)
      else if body.isAppOfArity ``HasSubset.Subset 4 then
        pure (.sub, body.getArg! 0, body.getArg! 2, body.getArg! 3)
      else if body.isAppOfArity ``Eq 3 then
        pure (.eq, body.getArg! 0, body.getArg! 1, body.getArg! 2)
      else return none
    -- the carrier type must (reducibly) be `Set (Formula _)`, i.e. `Logic _`
    let carrier ← whnfR carrier
    unless carrier.isAppOfArity ``Set 1 do return none
    unless (carrier.getArg! 0).isAppOf ``Formula do return none
    -- keep only inclusions between concrete logics, not generic lemmas
    unless (← isConcreteSide xs a) && (← isConcreteSide xs b) do return none
    -- ignore trivialities like `L ⊆ L` stated for rewriting purposes
    let sa := toString (← ppExpr a)
    let sb := toString (← ppExpr b)
    if sa == sb then return none
    return some ⟨sa, sb, t⟩

/-- Inclusions between logics of the `Neighborhood` library can only be stated
in its own modules, so the scan is restricted to constants coming from
`Neighborhood.*`: the rest of the environment (mathlib and the other
dependencies) is orders of magnitude larger, and feeding it through
`matchInclusion` dominates the running time of the whole extraction.
Constants surviving the module filter are further screened by the syntactic
`conclusionHead` check, so that `matchInclusion` only runs on candidates. -/
def collect : MetaM (Std.HashSet Edge) := do
  let env ← getEnv
  let modNames := env.header.moduleNames
  let heads : Std.HashSet Name :=
    .ofArray #[``HasSSubset.SSubset, ``HasSubset.Subset, ``Eq]
  let mut edges : Std.HashSet Edge := {}
  for (name, ci) in env.constants do
    if name.isInternal then continue
    let some modIdx := env.getModuleIdxFor? name | continue
    let modName := modNames.getD modIdx.toNat Name.anonymous
    unless (`Neighborhood).isPrefixOf modName do continue
    unless heads.contains (conclusionHead ci.type) do continue
    try
      if let some e ← matchInclusion ci then
        edges := edges.insert e
    catch _ => continue
  return edges

/-- Drop a `⊆` edge when the same inclusion is also known strictly or as an
equality. -/
def cleanDup (edges : Array Edge) : Array Edge :=
  edges.filter fun e =>
    match e.t with
    | .eq => true
    | .ssub => true
    | .sub => !edges.contains ⟨e.a, e.b, .ssub⟩ && !edges.contains ⟨e.a, e.b, .eq⟩

/-- The inclusion strengths derivable from `a` to `b` by composing edges along
paths of length ≥ 1 (equalities are symmetric, so they may be walked in both
directions). A depth-first search over `(node, accumulated strength)` states
replaces computing a full transitive closure: only the strength of a path
matters, and `EdgeType.comp` collapses it into one of three values, so the
state space is `3 × |nodes|`. -/
def reachableTypes (edges : Array Edge) (a b : String) : Std.HashSet EdgeType := Id.run do
  let mut adj : Std.HashMap String (Array (String × EdgeType)) := {}
  for e in edges do
    adj := adj.insert e.a ((adj.getD e.a #[]).push (e.b, e.t))
    if e.t == .eq then
      adj := adj.insert e.b ((adj.getD e.b #[]).push (e.a, .eq))
  let mut seen : Std.HashSet (String × EdgeType) := {}
  let mut stack : Array (String × EdgeType) := #[]
  for s in adj.getD a #[] do
    unless seen.contains s do
      seen := seen.insert s
      stack := stack.push s
  let mut out : Std.HashSet EdgeType := {}
  while _h : 0 < stack.size do
    let (n, t) := stack[stack.size - 1]
    stack := stack.pop
    if n == b then
      out := out.insert t
    for (n', t') in adj.getD n #[] do
      let s := (n', t.comp t')
      unless seen.contains s do
        seen := seen.insert s
        stack := stack.push s
  return out

/-- An edge is redundant when the surviving edges already derive an inclusion
at least as strong; drop such edges one at a time (transitive reduction).

The removal must be sequential, not a parallel filter: two edges can each be
derivable from the other via an equality (e.g. `EM ⊂ EMK` and `EM ⊂ EMCK`
with `EMK = EMCK`), and dropping both would disconnect the graph. -/
def reduce (edges : Array Edge) : Array Edge := Id.run do
  let mut keep := edges
  for e in edges do
    let rest := keep.filter (· != e)
    let ts := reachableTypes rest e.a e.b
    let derivable :=
      match e.t with
      | .eq => ts.contains .eq
      | .ssub => ts.contains .ssub
      | .sub => !ts.isEmpty
    if derivable then
      keep := rest
  return keep

def toJson (edges : Array Edge) : Json :=
  Json.arr <| edges.map fun ⟨a, b, t⟩ =>
    Json.mkObj [("from", a), ("to", b), ("type", toString t)]

def main : MetaM Unit := do
  let edges := (← collect).toArray
  let sorted := edges.qsort fun x y => x.a < y.a || (x.a == y.a && x.b < y.b)
  let reduced := reduce (cleanDup sorted)
  IO.println s!"collected: {edges.size} edges, after transitive reduction: {reduced.size}"
  IO.FS.writeFile "zoo/neighborhood.json" ((toJson reduced).pretty ++ "\n")

end Zoo

#eval Zoo.main
