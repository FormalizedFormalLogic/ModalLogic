# Neighborhood core redesign: `ProofHilbert` / `ProvableHilbert` / `Logic`

User instruction (2026-07-30, `MEMO.md`):

> ProvabilityLogic のように，まずは証明として `ProofHilbert` を定義し，`ProvableHilbert` を定義し，
> `Logic` を定義するようにしなさい．
> ProvabilityLogic のように，論理式は α によってパラメータ可能なものとしなさい．さらに Hilbert/Axiom は削除し，
> `{Axioms.M (.atom 0) (.atom 1)}` ではなく `Hilbert {Axioms.M A B | (A) (B)}` のように全ての論理式の
> インスタンスを入れて定義するようにしなさい．Hilbert の `axm` は substitution を考える必要はない．
> 論理式はギリシャ文字を使うのではなく，A, B, C といったラテン文字を使いなさい．

Reference implementation: `../SeqPL/ProvabilityLogic/{Formula/Basic,Hilbert/GL/Basic,Logic/Basic}.lean`.

Scope: the Foundation-free core only —
`Vorspiel.lean`, `Formula/{Basic,Subformulas}.lean`, `Axioms.lean`, `Logic/{Basic,Cl,Calculus,Context,MaximalConsistentSet}.lean`,
`Hilbert/{Basic,Logics}.lean`.
`Semantics/**` is still the Foundation-based port (namespace `LO.Modal.Neighborhood`, its own `LO.Modal.Formula`)
and is **not** touched here; its migration onto this core is the separate later task.

## Target design

### D1. `Formula` parameterised by `α`

```lean
inductive Formula (α : Type u)
  | atom   : α → Formula α
  | falsum : Formula α
  | imp    : Formula α → Formula α → Formula α
  | box    : Formula α → Formula α
  deriving DecidableEq

abbrev FormulaSet (α) := Set (Formula α)
abbrev FormulaFinset (α) := Finset (Formula α)
```

- Everything else in `Formula/Basic.lean` keeps its present shape: `Bot`/`Top` instances,
  the abbreviations `neg`/`or`/`and`/`dia`/`iff` (so `◇A = ∼□∼A` etc. stay `rfl`),
  the notations `∼ 🡒 ⋏ ⋎ 🡘 □ ◇`, `complexity`, `cases'`, `rec'`, `multibox`/`multidia` via
  `Function.iterate`, and the substitution API (`Substitution α := α → Formula α`).
- `Substitution` survives even though the new `axm` no longer uses it; it is part of the formula
  API and costs nothing. (Flag for the user: it currently has no consumer in the library.)
- Finset-valued declarations (`subformulas`, `FormulaFinset.conj`/`disj`, …) take `[DecidableEq α]`
  wherever they need it, as in SeqPL.

### D2. Latin metavariables

`φ ψ χ ξ ζ` → `A B C D` (and `A₁ A₂ B₁ B₂` for the indexed ones) in *all* core files:
`variable` blocks, binders, docstrings, comments. Sets keep `T U` (`FormulaSet`) and `Γ Δ`
(`FormulaFinset`). Lemma *names* (`C!_of_conseq!`, `and₁!`, …) are unchanged.
Do not use `E` as a formula variable — it is the name of the weakest logic.

### D3. Three layers, as in ProvabilityLogic

`Hilbert/Basic.lean`:

```lean
inductive ProofHilbert (Ax : FormulaSet α) : Formula α → Type u
  | axm {A} : A ∈ Ax → ProofHilbert Ax A          -- no substitution
  | mdp {A B} : ProofHilbert Ax (A 🡒 B) → ProofHilbert Ax A → ProofHilbert Ax B
  | re {A B} : ProofHilbert Ax (A 🡘 B) → ProofHilbert Ax (□A 🡘 □B)
  | implyK (A B) : ProofHilbert Ax (Axioms.ImplyK A B)
  | implyS (A B C) : ProofHilbert Ax (Axioms.ImplyS A B C)
  | dne (A) : ProofHilbert Ax (Axioms.DNE A)
  | andElim₁ (A B) | andElim₂ (A B) | andIntro (A B)
  | orIntro₁ (A B) | orIntro₂ (A B) | orElim (A B C)
notation:45 "⊢ʰ[" Ax "]! " A:46 => ProofHilbert Ax A

abbrev ProvableHilbert (Ax : FormulaSet α) (A : Formula α) : Prop := Nonempty (⊢ʰ[Ax]! A)
notation:45 "⊢ʰ[" Ax "] " A:46 => ProvableHilbert Ax A

abbrev Hilbert (Ax : FormulaSet α) : Logic α := { A | ⊢ʰ[Ax] A }
```

Carried over to the `ProvableHilbert` level (one `lemma` per constructor, as in SeqPL), plus
`@[simp] lemma mem_hilbert : A ∈ Hilbert Ax ↔ ⊢ʰ[Ax] A := Iff.rfl`, an `@[induction_eliminator]`
`ProvableHilbert.rec` proved by `rintro ⟨h⟩; induction h <;> grind`, and the two monotonicity
lemmas, now *without* any substitution step:

```lean
lemma Hilbert.subset_of_provable_axioms (h : Ax₁ ⊆ Hilbert Ax₂) : Hilbert Ax₁ ⊆ Hilbert Ax₂
lemma Hilbert.subset_of_subset_axioms  (h : Ax₁ ⊆ Ax₂)          : Hilbert Ax₁ ⊆ Hilbert Ax₂
```

`Hilbert.subst_mem` is **deleted** (its only purpose was the old substituting `axm`).

### D4. `Axiom` and the `Axiom.Has*` witness classes are deleted

`abbrev Axiom := Set Formula` and `Axiom.{HasM,HasC,HasN,HasK,HasT,HasB,HasD,HasP,HasFour,HasFive}`
(the classes carrying witnessing propositional variables `p`, `q` and `ne_pq`) go away, together with
the ten `instHasAxiom*` instances that recovered a scheme by substituting into its atomic instance.
Axiom sets are plain `FormulaSet α` containing *every* instance of the scheme, so the closure
conditions of `Logic/Calculus.lean` are obtained directly from `axm`, e.g.

```lean
instance : (EM (α := α)).HasAxiomM := ⟨fun A B => ⟨.axm (by simp)⟩⟩
```

Factor a `Hilbert.hasAxiomM_of (h : ∀ A B, Axioms.M A B ∈ Ax) : (Hilbert Ax).HasAxiomM`-style helper
per scheme only if the inline form turns out repetitive. (If Lean 4.31 rejects a `def` of class type,
mark it `@[reducible]`.)

### D5. Named logics (`Hilbert/Logics.lean`)

```lean
abbrev EM.axioms {α} : FormulaSet α := { Axioms.M A B | (A) (B) }
abbrev EM {α} : Logic α := Hilbert EM.axioms
```

and combinations by union of the single-scheme sets, e.g.
`abbrev EMC.axioms {α} : FormulaSet α := EM.axioms ∪ EC.axioms`,
`abbrev EMNT4.axioms {α} : FormulaSet α := EM.axioms ∪ EN.axioms ∪ ET.axioms ∪ E4.axioms`.
`Axioms.N` and `Axioms.P` are single formulas, so `EN.axioms := {Axioms.N}`, `EP.axioms := {Axioms.P}`.
The two coincidences `EMK_eq_EMCK` and `ETB_eq_ENTB` are re-proved through
`subset_of_subset_axioms` / `subset_of_provable_axioms` as before.

### D6. Unchanged in substance

`Logic/Basic.lean` (`abbrev Logic (α) := Set (Formula α)`, `Logic.Consistent`),
`Logic/Cl.lean` (the `Cl` closure class and the propositional toolkit over an abstract `L`),
`Logic/Calculus.lean` (`HasRE`, `HasAxiom*`, `rm!`, the derived schemes),
`Logic/Context.lean`, `Logic/MaximalConsistentSet.lean`, `Formula/Subformulas.lean`, `Vorspiel.lean`
keep their statements and proofs; they only gain the `α` parameter (and `[DecidableEq α]` where
Finsets demand it) and the Latin renaming.

## Steps (sequential; one commit each, module built before committing)

| # | File | Note |
|---|------|------|
| 1 | `Formula/Basic.lean` | D1 + D2 |
| 2 | `Formula/Subformulas.lean` | `[DecidableEq α]` |
| 3 | `Axioms.lean` | |
| 4 | `Logic/Basic.lean` | |
| 5 | `Logic/Cl.lean` | largest mechanical rename |
| 6 | `Logic/Calculus.lean` | |
| 7 | `Logic/Context.lean` | |
| 8 | `Logic/MaximalConsistentSet.lean` | |
| 9 | `Hilbert/Basic.lean` | rewrite (D3, D4) |
| 10 | `Hilbert/Logics.lean` | rewrite (D5) |
| 11 | — | `lake build Neighborhood`, `just mk-all`, `just shake`, rebuild |

Steps 1–8 break every downstream module at once, so each step is verified with
`lake build Neighborhood.<Module>` for its own module only; the whole-library build is step 11.

## Constraints

- No `sorry` may be introduced. No statement may be weakened: every lemma that exists today must
  exist after the refactor (modulo the deletions listed in D3/D4).
- `Semantics/**` must not be edited.
- `lake shake` reports four unrelated unused imports under `Fin74/Result/`; leave them alone
  (do not `git checkout` over them, do not bypass the plugin guardrails).
