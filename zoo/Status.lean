/-
Axiom status extractor for the `Neighborhood` library.

For every logic `Logic<X>` in the environment and every one of the ten axioms
`Axioms.<Z>`, records whether the axiom is

  * provable   — the instance `Logic.HasAxiom<Z> (@Logic<X> ℕ)` synthesizes,
  * refuted    — some theorem states that the axiom scheme is not in the logic,
                 i.e. its conclusion is `Axioms.<Z> … ∉ Logic<X> …` (possibly
                 under `∀`/`∃` binders), or
  * open       — neither, which is a gap in the formalization rather than a
                 claim about the logic.

Both sides are read off the statements, not off naming conventions, in the same
spirit as `zoo/Extract.lean`. The result is written to `zoo/status.json` and
rendered by `zoo/status.html`.

Run from the repository root:

    lake env lean zoo/Status.lean
-/
import Lean
import Neighborhood

open Lean Meta

namespace Status

/-- The ten axioms, in display order, as (constant suffix, label). `Axioms.Four`
and `Axioms.Five` are conventionally written `4` and `5`. -/
def axioms : Array (String × String) :=
  #[("K", "K"), ("M", "M"), ("C", "C"), ("N", "N"), ("T", "T"),
    ("B", "B"), ("D", "D"), ("P", "P"), ("Four", "4"), ("Five", "5")]

/-- Root-level constants `Logic<X>` (all-caps suffix) that apply to an atom type,
sorted by number of axioms in the name and then alphabetically. -/
def collectLogics : MetaM (Array Name) := do
  let env ← getEnv
  let mut ls : Array Name := #[]
  for (n, _) in env.constants do
    if n.isInternal then continue
    let s := n.toString
    unless s.startsWith "Logic" && s.length > 5 do continue
    unless (s.drop 5).all (fun c => c.isUpper || c.isDigit) do continue
    if (← try (do let _ ← mkAppOptM n #[mkConst ``Nat]; pure true) catch _ => pure false) then
      ls := ls.push n
  return ls.qsort fun a b =>
    let ka := (a.toString.drop 5).toString
    let kb := (b.toString.drop 5).toString
    ka.length < kb.length || (ka.length == kb.length && ka < kb)

/-- Strip the `∃` binders in front of a statement. -/
partial def stripExists (e : Expr) : MetaM Expr := do
  if e.isAppOfArity ``Exists 2 then
    lambdaTelescope (e.getArg! 1) fun _ b => stripExists b
  else
    return e

/-- Match a statement whose conclusion is `A ∉ L` with `L : Logic _` and `A` an
instance of one of the ten axiom schemes, returning `(axiom suffix, logic)`.

Like `zoo/Extract.lean`, the binders must be stripped with a non-reducing
`forallTelescope`: `∉` unfolds through `Set` membership, and the reducing
variant would telescope past the statement being matched. -/
def matchRefutation (ci : ConstantInfo) : MetaM (Option (String × Name)) := do
  forallTelescope ci.type fun _ body => do
    let body ← stripExists body
    let some inner := body.not? | return none
    let inner ← stripExists inner
    unless inner.isAppOfArity ``Membership.mem 5 do return none
    -- `Set` membership takes the collection first, the element second. Neither
    -- side may be reduced: the logics are `abbrev`s, so `whnfR` would unfold
    -- `LogicE4` to its Hilbert axiom set and lose the name being looked for.
    let logic := inner.getArg! 3
    let elem := inner.getArg! 4
    let some lname := logic.getAppFn.constName? | return none
    unless (lname.toString.startsWith "Logic") do return none
    let some ename := elem.getAppFn.constName? | return none
    unless (`Axioms).isPrefixOf ename do return none
    let some ax := axioms.find? (fun (suffix, _) => ename == (`Axioms).str suffix) | return none
    return some (ax.1, lname)

/-- Every `(axiom, logic)` pair refuted somewhere in `Neighborhood.*`, with the
name of a theorem witnessing it. -/
def collectRefutations : MetaM (Std.HashMap (String × Name) Name) := do
  let env ← getEnv
  let mut out : Std.HashMap (String × Name) Name := {}
  for (name, ci) in env.constants do
    if name.isInternal then continue
    let some modIdx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames.getD modIdx.toNat Name.anonymous
    unless (`Neighborhood).isPrefixOf modName do continue
    try
      if let some key ← matchRefutation ci then
        unless out.contains key do out := out.insert key name
    catch _ => continue
  return out

/-- The instance witnessing `Logic.HasAxiom<Z> (@Logic<X> ℕ)`, if it synthesizes. -/
def provableBy (logic : Name) (ax : String) : MetaM (Option Name) := do
  let L ← mkAppOptM logic #[mkConst ``Nat]
  let ty ← mkAppOptM ((`Logic).str ("HasAxiom" ++ ax)) #[mkConst ``Nat, L]
  let some e ← (try synthInstance? ty catch _ => pure none) | return none
  return (← instantiateMVars e).getAppFn.constName?

def main : MetaM Unit := do
  let logics ← collectLogics
  let refuted ← collectRefutations
  let mut rows : Array Json := #[]
  for lg in logics do
    let mut cells : Array (String × Json) := #[]
    for (suffix, label) in axioms do
      let cell ←
        if let some inst ← provableBy lg suffix then
          pure <| Json.mkObj [("status", true), ("ref", toString inst)]
        else if let some thm := refuted[(suffix, lg)]? then
          pure <| Json.mkObj [("status", false), ("ref", toString thm)]
        else
          -- nothing is known either way: a gap in the formalization
          pure Json.null
      cells := cells.push (label, cell)
    rows := rows.push <| Json.mkObj
      [("logic", Json.str (lg.toString.drop 5).toString), ("axioms", Json.mkObj cells.toList)]
  let out := Json.mkObj
    [ ("axioms", Json.arr (axioms.map fun (_, l) => Json.str l))
    , ("logics", Json.arr rows) ]
  IO.FS.writeFile "zoo/status.json" (out.pretty ++ "\n")
  IO.println s!"status: {logics.size} logics × {axioms.size} axioms"

end Status

set_option maxHeartbeats 4000000 in
#eval Status.main
