/-
Zoo extractor for the `Neighborhood` library.

Scans the environment for theorems whose statement has the form `L₁ ⊂ L₂` where
`L₁ L₂ : Logic _` (i.e. `Set (Formula _)`), reduces the collected strict-inclusion
graph by transitivity, and writes the remaining edges to `zoo/neighborhood.json`.

Run from the repository root:

    lake env lean zoo/Extract.lean
-/
import Lean
import Neighborhood

open Lean Meta

namespace Zoo

structure Edge where
  a : String
  b : String
deriving BEq, Hashable, Repr

/-- Match a statement of the form `L₁ ⊂ L₂` with `L₁ L₂ : Logic _`
(possibly under universally quantified binders), returning the pretty-printed
pair `(L₁, L₂)`. -/
def matchSSubset (ci : ConstantInfo) : MetaM (Option Edge) := do
  forallTelescopeReducing ci.type fun _ body => do
    unless body.isAppOfArity ``HasSSubset.SSubset 4 do return none
    -- the carrier type must (reducibly) be `Set (Formula _)`, i.e. `Logic _`
    let carrier ← whnfR (body.getArg! 0)
    unless carrier.isAppOfArity ``Set 1 do return none
    unless (carrier.getArg! 0).isAppOf ``Formula do return none
    let a := body.getArg! 2
    let b := body.getArg! 3
    return some ⟨toString (← ppExpr a), toString (← ppExpr b)⟩

def collect : MetaM (Std.HashSet Edge) := do
  let mut edges : Std.HashSet Edge := {}
  for (name, ci) in (← getEnv).constants do
    if name.isInternal then continue
    try
      if let some e ← matchSSubset ci then
        edges := edges.insert e
    catch _ => continue
  return edges

/-- `⊂` is transitive, so drop every edge that is recoverable as a composite of
two or more of the other edges (transitive reduction; the graph is acyclic
because `⊂` is irreflexive). -/
def reduce (edges : Array Edge) : Array Edge :=
  edges.filter fun e =>
    let rest := edges.filter (· != e)
    -- reachability from `e.a` to `e.b` through `rest`
    let rec go (frontier visited : List String) (fuel : Nat) : Bool :=
      match fuel with
      | 0 => false
      | fuel + 1 =>
        if frontier.contains e.b then true
        else
          let next := rest.toList.filterMap fun ⟨x, y⟩ =>
            if frontier.contains x && !visited.contains y then some y else none
          if next.isEmpty then false
          else go next.eraseDups (visited ++ next).eraseDups fuel
    !go [e.a] [e.a] (edges.size + 1)

def toJson (edges : Array Edge) : Json :=
  Json.arr <| edges.map fun ⟨a, b⟩ => Json.mkObj [("from", a), ("to", b)]

def main : MetaM Unit := do
  let edges := (← collect).toArray
  let sorted := edges.qsort fun x y => x.a < y.a || (x.a == y.a && x.b < y.b)
  let reduced := reduce sorted
  IO.println s!"collected: {edges.size} edges, after transitive reduction: {reduced.size}"
  IO.FS.writeFile "zoo/neighborhood.json" ((toJson reduced).pretty ++ "\n")

end Zoo

#eval Zoo.main
