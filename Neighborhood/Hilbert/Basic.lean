module

public import Neighborhood.Logic.Calculus

/-!
# Hilbert-style axiomatisation of classical non-normal modal logics

A `Hilbert`-style proof system is presented in three layers, following the pattern used
throughout the provability logic development:

* `ProofHilbert Ax A`, the `Type`-valued derivation tree of `A` from an axiom set `Ax`, closed
  under modus ponens and the congruence rule for `□`, together with the propositional axiom
  schemes `implyK`, `implyS`, `dne`, `andElim₁`, `andElim₂`, `andIntro`, `orIntro₁`, `orIntro₂`
  and `orElim`. Since `Ax` is a set of formulas rather than a set of schemes taken up to
  substitution, `axm` requires no substitution step: it is instantiated by supplying `Ax` with
  every instance of a scheme directly (e.g. `{Axioms.M A B | (A) (B)}`).
* `ProvableHilbert Ax A`, the `Prop`-valued truncation `Nonempty (ProofHilbert Ax A)`.
* `Hilbert Ax`, the `Logic` of formulas provable from `Ax`.
-/

@[expose] public section

variable {α : Type u}

/-- Derivations of `A` from the axiom set `Ax`, closed under modus ponens and the congruence rule
for `□`. Since `Ax` already contains every instance of each scheme it is meant to axiomatise,
`axm` need not perform a substitution. -/
inductive ProofHilbert (Ax : FormulaSet α) : Formula α → Type u
  | axm {A} : A ∈ Ax → ProofHilbert Ax A
  | mdp {A B} : ProofHilbert Ax (A 🡒 B) → ProofHilbert Ax A → ProofHilbert Ax B
  | re {A B} : ProofHilbert Ax (A 🡘 B) → ProofHilbert Ax (□A 🡘 □B)
  | implyK {A B} : ProofHilbert Ax (A 🡒 B 🡒 A)
  | implyS {A B C} : ProofHilbert Ax ((A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 A 🡒 C)
  | dne {A} : ProofHilbert Ax (∼∼A 🡒 A)
  | andElim₁ {A B} : ProofHilbert Ax (A ⋏ B 🡒 A)
  | andElim₂ {A B} : ProofHilbert Ax (A ⋏ B 🡒 B)
  | andIntro {A B} : ProofHilbert Ax (A 🡒 B 🡒 A ⋏ B)
  | orIntro₁ {A B} : ProofHilbert Ax (A 🡒 A ⋎ B)
  | orIntro₂ {A B} : ProofHilbert Ax (B 🡒 A ⋎ B)
  | orElim {A B C} : ProofHilbert Ax ((A 🡒 C) 🡒 (B 🡒 C) 🡒 (A ⋎ B 🡒 C))

@[inherit_doc] notation:45 "⊢ʰ[" Ax "]! " A:46 => ProofHilbert Ax A

/-- `A` is provable from the axiom set `Ax`. -/
abbrev ProvableHilbert (Ax : FormulaSet α) (A : Formula α) : Prop := Nonempty (⊢ʰ[Ax]! A)

@[inherit_doc] notation:45 "⊢ʰ[" Ax "] " A:46 => ProvableHilbert Ax A

variable {Ax Ax₁ Ax₂ : FormulaSet α} {A B C : Formula α}

namespace ProvableHilbert

@[grind ←] lemma axm (h : A ∈ Ax) : ⊢ʰ[Ax] A := ⟨ProofHilbert.axm h⟩
@[grind =>] lemma mdp : ⊢ʰ[Ax] (A 🡒 B) → ⊢ʰ[Ax] A → ⊢ʰ[Ax] B :=
  fun ⟨h₁⟩ ⟨h₂⟩ => ⟨ProofHilbert.mdp h₁ h₂⟩
@[grind <=] lemma re : ⊢ʰ[Ax] (A 🡘 B) → ⊢ʰ[Ax] (□A 🡘 □B) := fun ⟨h⟩ => ⟨ProofHilbert.re h⟩
@[simp, grind .] lemma implyK (A B) : ⊢ʰ[Ax] (A 🡒 B 🡒 A) := ⟨ProofHilbert.implyK⟩
@[simp, grind .] lemma implyS (A B C) : ⊢ʰ[Ax] ((A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 A 🡒 C) := ⟨ProofHilbert.implyS⟩
@[simp, grind .] lemma dne (A) : ⊢ʰ[Ax] (∼∼A 🡒 A) := ⟨ProofHilbert.dne⟩
@[simp, grind .] lemma andElim₁ (A B) : ⊢ʰ[Ax] (A ⋏ B 🡒 A) := ⟨ProofHilbert.andElim₁⟩
@[simp, grind .] lemma andElim₂ (A B) : ⊢ʰ[Ax] (A ⋏ B 🡒 B) := ⟨ProofHilbert.andElim₂⟩
@[simp, grind .] lemma andIntro (A B) : ⊢ʰ[Ax] (A 🡒 B 🡒 A ⋏ B) := ⟨ProofHilbert.andIntro⟩
@[simp, grind .] lemma orIntro₁ (A B) : ⊢ʰ[Ax] (A 🡒 A ⋎ B) := ⟨ProofHilbert.orIntro₁⟩
@[simp, grind .] lemma orIntro₂ (A B) : ⊢ʰ[Ax] (B 🡒 A ⋎ B) := ⟨ProofHilbert.orIntro₂⟩
@[simp, grind .] lemma orElim (A B C) : ⊢ʰ[Ax] ((A 🡒 C) 🡒 (B 🡒 C) 🡒 (A ⋎ B 🡒 C)) := ⟨ProofHilbert.orElim⟩

-- None of `axm`, `mdp`, `re`, `implyK`, `implyS`, `dne`, `andElim₁`, `andElim₂`, `andIntro`,
-- `orIntro₁`, `orIntro₂`, `orElim` is referenced by name inside `rintro A ⟨h⟩; induction h <;>
-- grind`, so the unused-variable linter would flag every parameter below. The names are not
-- dead: since `rec` is `@[induction_eliminator]`, they become the case tags used by
-- `induction ... using rec with | <name> ... => ...` at call sites, so they cannot be renamed
-- to `_` without breaking those call sites.
set_option linter.unusedVariables false in
/-- Induction on a derivation of `⊢ʰ[Ax] A`. -/
@[induction_eliminator]
lemma rec {motive : (A : Formula α) → ⊢ʰ[Ax] A → Prop}
    (axm : ∀ {A} (h : A ∈ Ax), motive A (axm h))
    (mdp : ∀ {A B} (h₁ : ⊢ʰ[Ax] (A 🡒 B)) (h₂ : ⊢ʰ[Ax] A),
      motive _ h₁ → motive _ h₂ → motive _ (mdp h₁ h₂))
    (re : ∀ {A B} (h : ⊢ʰ[Ax] (A 🡘 B)), motive _ h → motive _ (re h))
    (implyK : ∀ A B, motive _ (implyK A B))
    (implyS : ∀ A B C, motive _ (implyS A B C))
    (dne : ∀ A, motive _ (dne A))
    (andElim₁ : ∀ A B, motive _ (andElim₁ A B))
    (andElim₂ : ∀ A B, motive _ (andElim₂ A B))
    (andIntro : ∀ A B, motive _ (andIntro A B))
    (orIntro₁ : ∀ A B, motive _ (orIntro₁ A B))
    (orIntro₂ : ∀ A B, motive _ (orIntro₂ A B))
    (orElim : ∀ A B C, motive _ (orElim A B C)) :
    ∀ {A} (h : ⊢ʰ[Ax] A), motive A h := by
  rintro A ⟨h⟩
  induction h <;> grind

end ProvableHilbert

/-- The smallest logic containing every axiom of `Ax`, closed under modus ponens and the
congruence rule for `□`. -/
abbrev Hilbert (Ax : FormulaSet α) : Logic α := { A | ⊢ʰ[Ax] A }

namespace Hilbert

open Logic

instance : (Hilbert Ax).Cl where
  mdp := fun h₁ h₂ => ProvableHilbert.mdp h₁ h₂
  implyK := fun A B => ProvableHilbert.implyK A B
  implyS := fun A B C => ProvableHilbert.implyS A B C
  dne := fun A => ProvableHilbert.dne A
  andElim₁ := fun A B => ProvableHilbert.andElim₁ A B
  andElim₂ := fun A B => ProvableHilbert.andElim₂ A B
  andIntro := fun A B => ProvableHilbert.andIntro A B
  orIntro₁ := fun A B => ProvableHilbert.orIntro₁ A B
  orIntro₂ := fun A B => ProvableHilbert.orIntro₂ A B
  orElim := fun A B C => ProvableHilbert.orElim A B C

instance : (Hilbert Ax).HasRE where re := fun h => ProvableHilbert.re h

@[simp] lemma mem_hilbert : A ∈ Hilbert Ax ↔ ⊢ʰ[Ax] A := Iff.rfl

/-- If every axiom of `Ax₁` is provable in `Hilbert Ax₂`, then `Hilbert Ax₁ ⊆ Hilbert Ax₂`. -/
lemma subset_of_provable_axioms (h : Ax₁ ⊆ Hilbert Ax₂) : Hilbert Ax₁ ⊆ Hilbert Ax₂ := by
  intro A hA
  induction hA using ProvableHilbert.rec with
  | axm hmem => exact h hmem
  | mdp _ _ ih₁ ih₂ => exact ih₁ ⨀ ih₂
  | re _ ih => exact re ih
  | _ => simp

/-- Monotonicity of `Hilbert` in its axiom set. -/
lemma subset_of_subset_axioms (h : Ax₁ ⊆ Ax₂) : Hilbert Ax₁ ⊆ Hilbert Ax₂ :=
  subset_of_provable_axioms fun _ hA => ProvableHilbert.axm (h hA)

/-- `Hilbert Ax` has the axiom scheme `M` whenever `Ax` contains every instance of `M`. -/
lemma hasAxiomM_of (h : ∀ A B : Formula α, Axioms.M A B ∈ Ax) : (Hilbert Ax).HasAxiomM :=
  ⟨fun A B => ProvableHilbert.axm (h A B)⟩

/-- `Hilbert Ax` has the axiom scheme `C` whenever `Ax` contains every instance of `C`. -/
lemma hasAxiomC_of (h : ∀ A B : Formula α, Axioms.C A B ∈ Ax) : (Hilbert Ax).HasAxiomC :=
  ⟨fun A B => ProvableHilbert.axm (h A B)⟩

/-- `Hilbert Ax` has the axiom `N` whenever `Ax` contains it. -/
lemma hasAxiomN_of (h : Axioms.N ∈ Ax) : (Hilbert Ax).HasAxiomN :=
  ⟨ProvableHilbert.axm h⟩

/-- `Hilbert Ax` has the axiom scheme `K` whenever `Ax` contains every instance of `K`. -/
lemma hasAxiomK_of (h : ∀ A B : Formula α, Axioms.K A B ∈ Ax) : (Hilbert Ax).HasAxiomK :=
  ⟨fun A B => ProvableHilbert.axm (h A B)⟩

/-- `Hilbert Ax` has the axiom scheme `T` whenever `Ax` contains every instance of `T`. -/
lemma hasAxiomT_of (h : ∀ A : Formula α, Axioms.T A ∈ Ax) : (Hilbert Ax).HasAxiomT :=
  ⟨fun A => ProvableHilbert.axm (h A)⟩

/-- `Hilbert Ax` has the axiom scheme `B` whenever `Ax` contains every instance of `B`. -/
lemma hasAxiomB_of (h : ∀ A : Formula α, Axioms.B A ∈ Ax) : (Hilbert Ax).HasAxiomB :=
  ⟨fun A => ProvableHilbert.axm (h A)⟩

/-- `Hilbert Ax` has the axiom scheme `D` whenever `Ax` contains every instance of `D`. -/
lemma hasAxiomD_of (h : ∀ A : Formula α, Axioms.D A ∈ Ax) : (Hilbert Ax).HasAxiomD :=
  ⟨fun A => ProvableHilbert.axm (h A)⟩

/-- `Hilbert Ax` has the axiom `P` whenever `Ax` contains it. -/
lemma hasAxiomP_of (h : Axioms.P ∈ Ax) : (Hilbert Ax).HasAxiomP :=
  ⟨ProvableHilbert.axm h⟩

/-- `Hilbert Ax` has the axiom scheme `Four` whenever `Ax` contains every instance of `Four`. -/
lemma hasAxiomFour_of (h : ∀ A : Formula α, Axioms.Four A ∈ Ax) : (Hilbert Ax).HasAxiomFour :=
  ⟨fun A => ProvableHilbert.axm (h A)⟩

/-- `Hilbert Ax` has the axiom scheme `Five` whenever `Ax` contains every instance of `Five`. -/
lemma hasAxiomFive_of (h : ∀ A : Formula α, Axioms.Five A ∈ Ax) : (Hilbert Ax).HasAxiomFive :=
  ⟨fun A => ProvableHilbert.axm (h A)⟩

end Hilbert

end
