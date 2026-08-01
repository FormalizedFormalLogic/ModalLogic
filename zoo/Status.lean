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

Logics proved equal have the same status everywhere, so only one of them gets a
row of its own: the rest record which logic they are equal to. The one that
keeps the row is whichever comes first in the display order, that is, the one
axiomatised by the fewest axioms. Because the status is shared, the row is
filled from the evidence of the whole class rather than of its representative
alone: `LogicEMCN.not_provable_axiomT` settles `T` for `LogicENK` too, since
`LogicENK = LogicEMCN` is a theorem. The representative's own evidence is
preferred where it exists, so a fallback in the `ref` field is exactly a cell
that only an equal presentation of the logic records.

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

/-- Head constant of the conclusion of a (possibly universally quantified)
statement, read off syntactically without entering `MetaM`. Used to screen the
environment cheaply before the real matching runs. -/
def conclusionHead : Expr → Name
  | .forallE _ _ b _ => conclusionHead b
  | e => e.getAppFn.constName

/-- The `Logic<X>` constant an expression is headed by, if any. -/
def logicHead? (e : Expr) : Option Name := do
  let n ← e.getAppFn.constName?
  let s := n.toString
  guard <| s.startsWith "Logic" && s.length > 5 && (s.drop 5).all fun c => c.isUpper || c.isDigit
  return n

/-- Match a statement `L₁ = L₂` between two concrete logics (possibly under
universally quantified binders), as in `zoo/Extract.lean`. -/
def matchEquality (ci : ConstantInfo) : MetaM (Option (Name × Name)) := do
  forallTelescope ci.type fun _ body => do
    unless body.isAppOfArity ``Eq 3 do return none
    -- the carrier type must (reducibly) be `Set (Formula _)`, i.e. `Logic _`
    let carrier ← whnfR (body.getArg! 0)
    unless carrier.isAppOfArity ``Set 1 do return none
    unless (carrier.getArg! 0).isAppOf ``Formula do return none
    let some a := logicHead? (body.getArg! 1) | return none
    let some b := logicHead? (body.getArg! 2) | return none
    if a == b then return none
    return some (a, b)

/-- Every pair of logics proved equal somewhere in `Neighborhood.*`. -/
def collectEqualities : MetaM (Array (Name × Name)) := do
  let env ← getEnv
  let mut out : Array (Name × Name) := #[]
  for (name, ci) in env.constants do
    if name.isInternal then continue
    let some modIdx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames.getD modIdx.toNat Name.anonymous
    unless (`Neighborhood).isPrefixOf modName do continue
    unless conclusionHead ci.type == ``Eq do continue
    try
      if let some e ← matchEquality ci then out := out.push e
    catch _ => continue
  return out

/-- Map each logic to the representative of its equivalence class under provable
equality: the member coming first in `logics`, which is sorted by number of
axioms. Labels are propagated along the equalities until they stop moving; one
pass per logic is more than the longest chain can need. -/
def representatives (logics : Array Name) (eqs : Array (Name × Name)) :
    Std.HashMap Name Name := Id.run do
  let mut rank : Std.HashMap Name Nat := {}
  let mut rep : Std.HashMap Name Name := {}
  let mut i := 0
  for lg in logics do
    rank := rank.insert lg i
    rep := rep.insert lg lg
    i := i + 1
  for _ in [0:logics.size] do
    let mut changed := false
    for (a, b) in eqs do
      let some ra := rep[a]? | continue
      let some rb := rep[b]? | continue
      let some ia := rank[ra]? | continue
      let some ib := rank[rb]? | continue
      if ia < ib then
        rep := rep.insert b ra
        changed := true
      else if ib < ia then
        rep := rep.insert a rb
        changed := true
    unless changed do break
  return rep

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

/-- The instance witnessing `Logic.HasAxiom<Z> (@Logic<X> ℕ)`, if it synthesizes,
together with whether the axiom is *derived* rather than one of the axioms the
logic is defined by.

The two are told apart by where the instance is declared: the defining ones sit
next to the logic in `Neighborhood.Hilbert.*`, everything else is a consequence
proved in `Neighborhood.Logic.Calculus` (`LogicETB` proving `N` and `P`, say). -/
def provableBy (logic : Name) (ax : String) : MetaM (Option (Name × Bool)) := do
  let L ← mkAppOptM logic #[mkConst ``Nat]
  let ty ← mkAppOptM ((`Logic).str ("HasAxiom" ++ ax)) #[mkConst ``Nat, L]
  let some e ← (try synthInstance? ty catch _ => pure none) | return none
  let some inst := (← instantiateMVars e).getAppFn.constName? | return none
  let env ← getEnv
  let defining := match env.getModuleIdxFor? inst with
    | some idx => (`Neighborhood.Hilbert).isPrefixOf (env.header.moduleNames.getD idx.toNat .anonymous)
    | none => false
  return some (inst, !defining)

/-- The members of each equivalence class, keyed by its representative and listed
in display order, so that the representative itself comes first. -/
def classes (logics : Array Name) (reps : Std.HashMap Name Name) :
    Std.HashMap Name (Array Name) := Id.run do
  let mut out : Std.HashMap Name (Array Name) := {}
  for lg in logics do
    let rep := reps[lg]?.getD lg
    out := out.insert rep ((out[rep]?.getD #[]).push lg)
  return out

def main : MetaM Unit := do
  let logics ← collectLogics
  let refuted ← collectRefutations
  let reps := representatives logics (← collectEqualities)
  let members := classes logics reps
  let mut rows : Array Json := #[]
  let mut equiv := 0
  for lg in logics do
    let name := Json.str (lg.toString.drop 5).toString
    -- a logic equal to an earlier one has the same status everywhere
    if let some rep := reps[lg]? then
      if rep != lg then
        rows := rows.push <| Json.mkObj
          [("logic", name), ("equivalentTo", Json.str (rep.toString.drop 5).toString)]
        equiv := equiv + 1
        continue
    let mems := members[lg]?.getD #[lg]
    let mut cells : Array (String × Json) := #[]
    for (suffix, label) in axioms do
      -- any member of the class settles the cell; the representative goes first
      let mut cell : Option Json := none
      for m in mems do
        if cell.isSome then continue
        if let some (inst, derived) ← provableBy m suffix then
          cell := some <| Json.mkObj
            [("status", true), ("derived", derived), ("ref", toString inst)]
      for m in mems do
        if cell.isSome then continue
        if let some thm := refuted[(suffix, m)]? then
          cell := some <| Json.mkObj [("status", false), ("ref", toString thm)]
      -- nothing is known either way: a gap in the formalization
      cells := cells.push (label, cell.getD Json.null)
    rows := rows.push <| Json.mkObj [("logic", name), ("axioms", Json.mkObj cells.toList)]
  let out := Json.mkObj
    [ ("axioms", Json.arr (axioms.map fun (_, l) => Json.str l))
    , ("logics", Json.arr rows) ]
  IO.FS.writeFile "zoo/status.json" (out.pretty ++ "\n")
  IO.println s!"status: {logics.size - equiv} logics × {axioms.size} axioms, \
    {equiv} equal to an earlier logic"

end Status

set_option maxHeartbeats 4000000 in
#eval Status.main
