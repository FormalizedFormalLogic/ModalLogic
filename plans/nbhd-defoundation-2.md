# Neighborhood: full removal of the Foundation dependency

User instructions (2026-07-30):

> LO.Modal namespace がまだ残っているので削除しなさい．さらに，ProvabilityLogic のようにフレームは
> κ : Type* 上に定める構造だとするリファクタリングを入れなさい．Entailment.Sound や Entailment.Complete
> などの，Foundation の定義に依存するものがまだ残っている．これも ProvabilityLogic のようにステートメントを
> 書き下すようにしなさい．フレームクラスという概念は削除しなさい．Propositional Logic の ImplyK のような
> 命題論理の公理はいちいち書きたくないので削除しなさい．LO.Modal.ED ではなく，LogicED としなさい．ほか同様．
> とにかく，Foundation の依存は全て削除しなさい．積極的なリファクタリングを行え．

Reference: `../SeqPL/ProvabilityLogic/Kripke/Basic.lean` (the `Model κ α` / `Forces` / `⊩` / `⊧`
pattern), `Logic/GL/Basic.lean` (plain soundness/completeness statements quantified over the
carrier).

Supersedes the remaining executable content of `plans/nbhd-defoundation.md` and
`plans/nbhd-kappa-parameterization.md`; the design decisions recorded there (predicate frame
class, `Sound`/`Complete` type classes) are all void — this plan is the contract.

## Global rules

- **No Foundation import anywhere under `Neighborhood/`.** `lakefile.toml` keeps the Foundation
  require (Fin74 uses it), but no `Neighborhood` module mentions `Foundation` or `LO.`.
- **No namespace `LO.Modal` / `LO.Modal.Neighborhood`.** Everything top level, matching the core
  (`Formula`, `Logic`, `Hilbert`, …) and SeqPL. Inner namespaces (`Frame`, `Model`, …) only.
- **No `FrameClass`**, no `ValidOnFrameClass`, no `Frame.logic`/`FrameClass.logic`.
- **No `Sound`/`Complete`/`Semantics`/`Entailment` type classes.** Soundness, completeness,
  consistency and inclusion facts are plain `theorem`s (consistency may use the core's
  `Logic.Consistent` class, which is ours).
- Formula metavariables are Latin `A B C D`; worlds `x y z`; sets of worlds `X Y Z`;
  valuations `V`; logics `L`.
- Aggressive refactoring is wanted: do not preserve Foundation idioms, dead generality, or
  awkward proofs; restate cleanly and prove with modern tactics (`grind`, `tauto_set`, `simp`).

## D1. Core: drop the propositional axiom schemes (`Axioms.*`)

Delete from `Neighborhood/Axioms.lean`: `ImplyK`, `ImplyS`, `ElimContra`, `DNE`, `AndElim₁`,
`AndElim₂`, `AndIntro`, `OrIntro₁`, `OrIntro₂`, `OrElim`. Keep the modal schemes
(`K M C N T B D P Four Five Geach`). Write the propositional formulas inline where they were
used, exactly as SeqPL does:

- `ProofHilbert` constructors: `| implyK {A B} : ProofHilbert Ax (A 🡒 B 🡒 A)` etc.
- `Logic.Cl` fields: `implyK : ∀ A B : Formula α, A 🡒 B 🡒 A ∈ L` etc.
- The corresponding `ProvableHilbert` lemmas and `Cl` accessor lemmas restate the formulas
  inline; names unchanged.

Also delete `Substitution`, `Formula.subst`, `Substitution.id`, `Substitution.comp` and all
`subst` lemmas from `Formula/Basic.lean` — with the substitution-free `axm` nothing uses them
(soundness no longer needs `ValidOnFrame.subst` either).

## D2. Core: rename the named logics `X` → `LogicX`

In `Neighborhood/Hilbert/Logics.lean`: `E` → `LogicE`, `EM` → `LogicEM`, …, `ET5` → `LogicET5`
(all 30), axiom sets `LogicEM.axioms` etc., coincidence theorems
`LogicEMK_eq_LogicEMCK`, `LogicETB_eq_LogicENTB`.

## D3. Semantics base (`Semantics/Basic.lean`), rewritten from scratch

```lean
structure Frame (κ : Type u) [Nonempty κ] where
  𝒩 : κ → Set (Set κ)

namespace Frame
abbrev World (_ : Frame κ) := κ                    -- the SeqPL trick: x : F.World fixes F
def box (F : Frame κ) : Set κ → Set κ := fun X => { x | X ∈ F.𝒩 x }
def dia (F : Frame κ) : Set κ → Set κ := fun X => (F.box Xᶜ)ᶜ
def mk_ℬ (B : Set κ → Set κ) : Frame κ := ⟨fun x => { X | x ∈ B X }⟩
class IsFinite (F : Frame κ) : Prop where world_finite : Finite κ
abbrev simple_blackhole : Frame Unit := ⟨fun _ => {Set.univ}⟩
-- eq_ℬ_𝒩 and the other generic box/dia lemmas carry over, κ-parameterised

structure Model (κ : Type u) [Nonempty κ] (α : Type v) extends Frame κ where
  Val : α → Set κ

def Model.truthset (M : Model κ α) : Formula α → Set κ   -- CoeFun `M A` as before
def Forces {M : Model κ α} (x : M.World) (A : Formula α) : Prop := x ∈ M.truthset A
infix:55 " ⊩ " => Forces                            -- x ⊮ A for the negation
def Model.Validate (M : Model κ α) (A : Formula α) : Prop := ∀ x : M.World, x ⊩ A
infix:50 " ⊧ " => Model.Validate
def Frame.Validate (F : Frame κ) (A : Formula α) : Prop := ∀ V, (⟨F, V⟩ : Model κ α) ⊧ A
infix:50 " ⊧ " => Frame.Validate                    -- overloaded, resolved by type
```

Truthset simp lemmas (`eq_atom` … `eq_diaItr`), `Forces` lemmas (`forces_imp`, `forces_box`, …
`@[grind =]` like SeqPL), `Model.Validate.mdp`/`.re`, `Frame.Validate.mdp`/`.re`,
`valid_iff : M ⊧ A 🡘 B ↔ M.truthset A = M.truthset B`,
`Frame.Validate.not_bot : ¬F ⊧ (⊥ : Formula α)` — no `Semantics`/`Tarski` instances, no
`Axioms.ImplyK` validity lemmas (nothing named to validate), no `subst`.

## D4. `Semantics/Hilbert.lean`: soundness as one plain theorem

```lean
theorem Hilbert.sound {Ax : FormulaSet α} (hAx : ∀ B ∈ Ax, F ⊧ B) :
    A ∈ Hilbert Ax → F ⊧ A
```
by induction on `ProvableHilbert` (`axm` case is `hAx`, no substitution; the nine propositional
constructor cases are `fun x => by grind`-style validities). Also the consistency helper:
```lean
theorem Hilbert.not_mem_of_not_valid (hAx : ∀ B ∈ Ax, F ⊧ B) (h : ¬F ⊧ A) : A ∉ Hilbert Ax
```
No `Sound` instances, no frame classes.

## D5. `Semantics/Completeness.lean`: canonical model over the core MCS

`proofset L A : Set (MaximalConsistentSet L)` and its algebra (rewritten from the Foundation
version onto the core's `MaximalConsistentSet`, using the core `Logic.Cl`/`HasRE` API — the old
`Entailment.E 𝓢` becomes `[L.Cl] [L.HasRE]`, `Entailment.EM` adds `[L.HasAxiomM]`).
`Canonicity L` with `𝒩 : MCS L → Set (Set (MCS L))`, `def_𝒩`, `V`, `def_V`;
`Canonicity.toModel : Model (MaximalConsistentSet L) α` (needs `[L.Consistent]` for
`Nonempty`); `truthlemma`; `basicCanonicity`, `relativeBasicCanonicity`,
`minimal/maximalRelativeMaximalCanonicity` as before, κ-typed. The generic completeness
producer is statement-shaped, not a class:
```lean
theorem Canonicity.mem_of_valid (𝓒 : Canonicity L) (h : 𝓒.toModel ⊧ A) : A ∈ L
```
(contrapositive via Lindenbaum, as the old `Canonicity.completeness`), from which each logic
file concludes `(∀ frames with conditions, F ⊧ A) → A ∈ LogicX` by checking the canonical
frame's conditions.

## D6. Axiom files (`AxiomM/C/N/K/P/Geach`)

Keep the frame-condition classes (`Frame.IsMonotonic`, `IsRegular`, `ContainsUnit`, `IsFilter`,
`ContainsEmpty`?, Geach family …) on `Frame κ`, their closure lemmas, and the two directions
per axiom, restated without frame classes:

```lean
theorem valid_axiomM_of_isMonotonic [F.IsMonotonic] : F ⊧ Axioms.M A B      -- for all A B now
theorem isMonotonic_of_valid_axiomM (h : ∀ A B : Formula ℕ, F ⊧ Axioms.M A B) : F.IsMonotonic
```
(The definability direction may keep whatever atom-instance hypothesis it actually needs —
match the old statement's strength, e.g. `F ⊧ Axioms.M (.atom 0) (.atom 1)` with a fixed
valuation argument works only when `α` supplies two atoms; state it over `Formula ℕ` as before.)

## D7. `Supplementation`, `IntersectionClosure`, `Filtration`

Same mathematical content, κ-parameterised, Foundation-free. Constructions become
`Frame.supplementation : Frame κ → Frame κ` etc.; filtration quotients live over
`FilterEqvQuotient M T : Type` with `Model (FilterEqvQuotient M T) α`. The κ plan predicted the
`toModel`-type-splitting defeq issues largely disappear since `World` is a reducible abbrev.

## D8. The 28 logic files + `Incomparability/ED_EP.lean`

Per logic `X` (template: `Logic/E.lean`, written first):

- Frame condition aliases stay (`Frame.IsE4` etc. where they exist).
- Soundness: `theorem LogicX.sound (h : A ∈ LogicX) {κ} [Nonempty κ] (F : Frame κ)
  [F.Is…] … : F ⊧ A` — via `Hilbert.sound` + the axiom-validity lemmas.
- Consistency: `instance : (LogicX (α := α)).Consistent` via a countermodel frame.
- Completeness (where the old file had it): `theorem LogicX.complete
  (h : ∀ {κ : Type} [Nonempty κ] (F : Frame κ), F.Is… → F ⊧ A) : A ∈ LogicX` via
  `Canonicity.mem_of_valid` after equipping the canonical frame with the conditions.
- Finite frame property (the 8 filtration logics): plain theorems quantifying over
  `[F.IsFinite]` frames.
- Inclusions: `theorem LogicE_ssubset_LogicEM : @LogicE ℕ ⊂ LogicEM` — `⊆` via
  `Hilbert.subset_of_subset_axioms`-style reasoning, `≠` via an explicit countermodel
  (`Frame (Fin n)` with a concrete `𝒩`) and soundness. Same for every `⪱` fact in the old
  files; `Incomparable` in `ED_EP` becomes two non-inclusion theorems.
- **Placement (user instruction 2026-07-30, recorded in `contribute/style.md`)**: a
  strict-inclusion lemma lives in the *stronger* logic's module — `LogicE_ssubset_LogicEM`
  is in `Logic/EM.lean`, not `Logic/E.lean`. Old files stated `X ⪱ Y` in scattered places;
  redistribute by the larger side. Old `EM ⪱ EMCK` (EMCK has no module) stays in `EMK.lean`
  next to the coincidence `LogicEMK_eq_LogicEMCK`.
- **Annotation style (user instruction 2026-07-30, ditto)**: `@LogicE α` / `@LogicE ℕ`,
  never `LogicE (α := α)`; and no annotation at all when the type is inferable.

Countermodels change shape from `⟨World := Fin 3, 𝒩, Val⟩` to
`M : Model (Fin 3) ℕ := ⟨⟨𝒩⟩, Val⟩`.

## Execution

Wave 1 (parallel): (a) D1 core cleanup, (b) D2 rename, (c) D3 new `Basic.lean`.
Wave 2 (parallel, after 1): D4 `Hilbert`, D5 `Completeness`, D6 six axiom files,
D7 `Supplementation` + `IntersectionClosure`.
Wave 3: D7 `Filtration`; D8 template `Logic/E.lean`.
Wave 4 (parallel): remaining 27 logic files + `ED_EP`.
Then `just mk-all`, scoped shake, full build, PR update.

Agents write without building (coordinator builds per wave and dispatches fixes); each agent
owns its listed files exclusively.
