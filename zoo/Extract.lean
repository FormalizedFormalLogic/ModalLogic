/-
Zoo extractor for the `Neighborhood` library.

Scans the environment for theorems whose statement has the form `L₁ ⊂ L₂`,
`L₁ ⊆ L₂` or `L₁ = L₂` where `L₁ L₂ : Logic _` (i.e. `Set (Formula _)`),
reduces the collected inclusion graph by transitivity, and writes the
remaining edges to `zoo/zoo.json`.

A second, smaller graph is written to `zoo/compact.json`: the same relation
restricted to the extensions of `E` by `M`, `C`, `N`, `D`, `T`, `B`, `4`, `5`,
with each equivalence class of logics collapsed to a single representative.

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

/-- How much an edge says, used to pick the most informative of several
inclusions derivable between the same two logics. Mirrors `cleanDup`: a `⊆`
edge is the weakest statement, and `⊂` and `=` (which cannot both hold) are
equally strong. -/
def EdgeType.rank : EdgeType → Nat
  | .sub => 0
  | .ssub => 1
  | .eq => 1

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

/-! ### The compact zoo

The full zoo carries every logic the library knows about, including the
extensions by `P` and `K` and every member of an equivalence class. The
compact zoo keeps only the extensions of `E` by `M`, `C`, `N`, `D`, `T`, `B`,
`4`, `5`, and only one representative per equivalence class. -/

/-- The axioms an extension of `E` may be built from to appear in the compact
zoo; `P` and `K` are deliberately absent. -/
def compactAxioms : List Char := ['M', 'C', 'N', 'D', 'T', 'B', '4', '5']

/-- Whether a logic belongs to the compact zoo, read off its name: `LogicE`
followed by axioms drawn from `compactAxioms`. -/
def isCompact (name : String) : Bool :=
  name.startsWith "LogicE" && (name.drop 6).all (compactAxioms.contains ·)

/-- Partition the nodes into equivalence classes along the `eq` edges, keying
each class by the alphabetically first of its members. -/
def eqClasses (edges : Array Edge) : Std.HashMap String String × Std.HashMap String (Array String) :=
  Id.run do
    let mut nodes : Std.HashSet String := {}
    let mut adj : Std.HashMap String (Array String) := {}
    for e in edges do
      nodes := (nodes.insert e.a).insert e.b
      if e.t == .eq then
        adj := adj.insert e.a ((adj.getD e.a #[]).push e.b)
        adj := adj.insert e.b ((adj.getD e.b #[]).push e.a)
    let mut key : Std.HashMap String String := {}
    let mut members : Std.HashMap String (Array String) := {}
    for n in nodes do
      if key.contains n then continue
      let mut seen : Std.HashSet String := {n}
      let mut stack : Array String := #[n]
      let mut cls : Array String := #[]
      while _h : 0 < stack.size do
        let m := stack[stack.size - 1]
        stack := stack.pop
        cls := cls.push m
        for m' in adj.getD m #[] do
          unless seen.contains m' do
            seen := seen.insert m'
            stack := stack.push m'
      let k := cls.foldl (fun a b => if b < a then b else a) n
      for m in cls do key := key.insert m k
      members := members.insert k cls
    return (key, members)

/-- The name an equivalence class goes by in the compact zoo: the shortest of
its members that belongs to the compact zoo at all, ties broken
alphabetically. A class none of whose members qualifies (e.g. the singleton
`EK`) has no representative and drops out. -/
def chooseRep (members : Array String) : Option String :=
  members.foldl (init := none) fun best n =>
    if !isCompact n then best
    else match best with
      | none => some n
      | some b => if n.length < b.length || (n.length == b.length && n < b) then some n else some b

/-- The inclusion strengths derivable from `a` to each other node, by paths of
length ≥ 1. This is `reachableTypes` for all targets at once, keeping only the
strongest strength found; the compact zoo needs the whole row, and one search
per source is markedly cheaper than one per pair. -/
def reachableFrom (edges : Array Edge) (a : String) : Std.HashMap String EdgeType := Id.run do
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
  let mut out : Std.HashMap String EdgeType := {}
  while _h : 0 < stack.size do
    let (n, t) := stack[stack.size - 1]
    stack := stack.pop
    match out[n]? with
    | some t' => if t'.rank < t.rank then out := out.insert n t
    | none => out := out.insert n t
    for (n', t') in adj.getD n #[] do
      let s := (n', t.comp t')
      unless seen.contains s do
        seen := seen.insert s
        stack := stack.push s
  return out

/-- Collapse each equivalence class to a single representative and drop the
logics outside the compact zoo, then reduce the result by transitivity.
Returns the surviving representatives along with the edges between them.

Inclusions are re-derived from the transitive closure of the quotient graph
rather than by relabelling the given edges: a discarded class can sit in the
middle of a chain (`E ⊂ EK ⊂ EMK`), and simply dropping its edges would lose
the inclusions that pass through it.

The representatives are reported separately because collapsing a class can
leave one with no edges at all: a logic whose only known relations are the
equalities to its own class members keeps none of them, and an edge list
alone would silently lose it. -/
def compact (edges : Array Edge) : Array String × Array Edge := Id.run do
  let (key, members) := eqClasses edges
  let mut rep : Std.HashMap String String := {}
  for (k, ms) in members do
    if let some r := chooseRep ms then rep := rep.insert k r
  let mut quotient : Std.HashSet Edge := {}
  for e in edges do
    let ka := key.getD e.a e.a
    let kb := key.getD e.b e.b
    unless ka == kb do quotient := quotient.insert ⟨ka, kb, e.t⟩
  let qedges := quotient.toArray
  let mut closure : Array Edge := #[]
  for (k, r) in rep do
    for (k', t) in reachableFrom qedges k do
      if let some r' := rep[k']? then
        unless r == r' do closure := closure.push ⟨r, r', t⟩
  let sorted := closure.qsort fun x y => x.a < y.a || (x.a == y.a && x.b < y.b)
  let nodes := rep.valuesArray.qsort (· < ·)
  return (nodes, reduce sorted)

/-- The height of each logic in the compact zoo: the length of the longest
chain of inclusions leading up to it, so that `E` sits at level `0`.

The renderer pins every logic of a given level to one row, which turns the
drawing into a properly graded Hasse diagram; left to itself, the layout
engine ranks by a criterion of its own and the result is a tangle. -/
def levels (nodes : Array String) (edges : Array Edge) : Std.HashMap String Nat := Id.run do
  let mut lvl : Std.HashMap String Nat := nodes.foldl (fun m v => m.insert v 0) {}
  let mut changed := true
  while changed do
    changed := false
    for e in edges do
      let below := lvl.getD e.a 0 + 1
      if lvl.getD e.b 0 < below then
        lvl := lvl.insert e.b below
        changed := true
  return lvl

def edgesToJson (edges : Array Edge) : Json :=
  Json.arr <| edges.map fun ⟨a, b, t⟩ =>
    Json.mkObj [("from", a), ("to", b), ("type", toString t)]

def compactToJson (nodes : Array String) (edges : Array Edge) : Json :=
  let lvl := levels nodes edges
  Json.mkObj
    [ ("nodes", Json.arr <| nodes.map fun n =>
        Json.mkObj [("name", Json.str n), ("level", Json.num (lvl.getD n 0))])
    , ("edges", edgesToJson edges) ]

def main : MetaM Unit := do
  let edges := (← collect).toArray
  let sorted := edges.qsort fun x y => x.a < y.a || (x.a == y.a && x.b < y.b)
  let reduced := reduce (cleanDup sorted)
  IO.println s!"collected: {edges.size} edges, after transitive reduction: {reduced.size}"
  IO.FS.writeFile "zoo/zoo.json" ((edgesToJson reduced).pretty ++ "\n")
  let (nodes, compacted) := compact reduced
  IO.println s!"compact zoo: {nodes.size} logics, {compacted.size} edges"
  IO.FS.writeFile "zoo/compact.json" ((compactToJson nodes compacted).pretty ++ "\n")

end Zoo

#eval Zoo.main
