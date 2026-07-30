module

public import Neighborhood.Logic.Calculus

/-!
# Hilbert-style axiomatisation of classical non-normal modal logics

A set of axiom schemes and the smallest logic containing all of their substitution instances,
closed under modus ponens and the congruence rule for `□`. Possession of a named axiom scheme by
the set of schemes is expressed by a class carrying witnessing propositional variables, from which
the corresponding closure condition of the generated logic follows by substitution.
-/

@[expose] public section

namespace LO.Modal

/-- A set of axiom schemes, each taken up to substitution. -/
abbrev Axiom := Set Formula

namespace Axiom

/-- `Ax` contains the axiom scheme `M`, witnessed by two distinct propositional variables. -/
class HasM (Ax : Axiom) where
  p : ℕ
  q : ℕ
  ne_pq : p ≠ q := by trivial
  mem_M : Axioms.M (.atom p) (.atom q) ∈ Ax := by tauto

/-- `Ax` contains the axiom scheme `C`, witnessed by two distinct propositional variables. -/
class HasC (Ax : Axiom) where
  p : ℕ
  q : ℕ
  ne_pq : p ≠ q := by trivial
  mem_C : Axioms.C (.atom p) (.atom q) ∈ Ax := by tauto

/-- `Ax` contains the axiom `N`. -/
class HasN (Ax : Axiom) where
  mem_N : Axioms.N ∈ Ax := by tauto

/-- `Ax` contains the axiom scheme `K`, witnessed by two distinct propositional variables. -/
class HasK (Ax : Axiom) where
  p : ℕ
  q : ℕ
  ne_pq : p ≠ q := by trivial
  mem_K : Axioms.K (.atom p) (.atom q) ∈ Ax := by tauto

/-- `Ax` contains the axiom scheme `T`, witnessed by a propositional variable. -/
class HasT (Ax : Axiom) where
  p : ℕ
  mem_T : Axioms.T (.atom p) ∈ Ax := by tauto

/-- `Ax` contains the axiom scheme `B`, witnessed by a propositional variable. -/
class HasB (Ax : Axiom) where
  p : ℕ
  mem_B : Axioms.B (.atom p) ∈ Ax := by tauto

/-- `Ax` contains the axiom scheme `D`, witnessed by a propositional variable. -/
class HasD (Ax : Axiom) where
  p : ℕ
  mem_D : Axioms.D (.atom p) ∈ Ax := by tauto

/-- `Ax` contains the axiom `P`. -/
class HasP (Ax : Axiom) where
  mem_P : Axioms.P ∈ Ax := by tauto

/-- `Ax` contains the axiom scheme `Four`, witnessed by a propositional variable. -/
class HasFour (Ax : Axiom) where
  p : ℕ
  mem_Four : Axioms.Four (.atom p) ∈ Ax := by tauto

/-- `Ax` contains the axiom scheme `Five`, witnessed by a propositional variable. -/
class HasFive (Ax : Axiom) where
  p : ℕ
  mem_Five : Axioms.Five (.atom p) ∈ Ax := by tauto

end Axiom

/-- The smallest logic containing every substitution instance of `Ax`, closed under modus ponens
and the congruence rule for `□`. -/
inductive Hilbert (Ax : Axiom) : Logic
  | axm {φ} (s : Substitution) : φ ∈ Ax → Hilbert Ax (φ⟦s⟧)
  | mdp {φ ψ} : Hilbert Ax (φ 🡒 ψ) → Hilbert Ax φ → Hilbert Ax ψ
  | re {φ ψ} : Hilbert Ax (φ 🡘 ψ) → Hilbert Ax (□φ 🡘 □ψ)
  | implyK φ ψ : Hilbert Ax (Axioms.ImplyK φ ψ)
  | implyS φ ψ χ : Hilbert Ax (Axioms.ImplyS φ ψ χ)
  | dne φ : Hilbert Ax (Axioms.DNE φ)
  | andElim₁ φ ψ : Hilbert Ax (Axioms.AndElim₁ φ ψ)
  | andElim₂ φ ψ : Hilbert Ax (Axioms.AndElim₂ φ ψ)
  | andIntro φ ψ : Hilbert Ax (Axioms.AndIntro φ ψ)
  | orIntro₁ φ ψ : Hilbert Ax (Axioms.OrIntro₁ φ ψ)
  | orIntro₂ φ ψ : Hilbert Ax (Axioms.OrIntro₂ φ ψ)
  | orElim φ ψ χ : Hilbert Ax (Axioms.OrElim φ ψ χ)

namespace Hilbert

open Logic

variable {Ax Ax₁ Ax₂ : Axiom} {φ ψ : Formula} {s : Substitution}

instance : (Hilbert Ax).Cl where
  mdp := Hilbert.mdp
  implyK := Hilbert.implyK
  implyS := Hilbert.implyS
  dne := Hilbert.dne
  andElim₁ := Hilbert.andElim₁
  andElim₂ := Hilbert.andElim₂
  andIntro := Hilbert.andIntro
  orIntro₁ := Hilbert.orIntro₁
  orIntro₂ := Hilbert.orIntro₂
  orElim := Hilbert.orElim

instance : (Hilbert Ax).HasRE where re := Hilbert.re

@[grind ←] lemma axm! (s : Substitution) (h : φ ∈ Ax) : φ⟦s⟧ ∈ Hilbert Ax := axm s h

@[grind ←] lemma axm'! (h : φ ∈ Ax) : φ ∈ Hilbert Ax := by simpa using axm! .id h

/-- Provability in a Hilbert system is closed under substitution. -/
lemma subst_mem (h : φ ∈ Hilbert Ax) : φ⟦s⟧ ∈ Hilbert Ax := sorry

/-- Induction on a proof in a Hilbert system. -/
protected lemma rec! {motive : Formula → Prop}
    (axm : ∀ {φ} (s : Substitution), φ ∈ Ax → motive (φ⟦s⟧))
    (mdp : ∀ {φ ψ}, φ 🡒 ψ ∈ Hilbert Ax → φ ∈ Hilbert Ax → motive (φ 🡒 ψ) → motive φ → motive ψ)
    (re : ∀ {φ ψ}, φ 🡘 ψ ∈ Hilbert Ax → motive (φ 🡘 ψ) → motive (□φ 🡘 □ψ))
    (implyK : ∀ φ ψ, motive (Axioms.ImplyK φ ψ))
    (implyS : ∀ φ ψ χ, motive (Axioms.ImplyS φ ψ χ))
    (dne : ∀ φ, motive (Axioms.DNE φ))
    (andElim₁ : ∀ φ ψ, motive (Axioms.AndElim₁ φ ψ))
    (andElim₂ : ∀ φ ψ, motive (Axioms.AndElim₂ φ ψ))
    (andIntro : ∀ φ ψ, motive (Axioms.AndIntro φ ψ))
    (orIntro₁ : ∀ φ ψ, motive (Axioms.OrIntro₁ φ ψ))
    (orIntro₂ : ∀ φ ψ, motive (Axioms.OrIntro₂ φ ψ))
    (orElim : ∀ φ ψ χ, motive (Axioms.OrElim φ ψ χ))
    (h : φ ∈ Hilbert Ax) : motive φ := sorry

/-- If every scheme of `Ax₁` is provable in `Hilbert Ax₂`, then `Hilbert Ax₁` is contained in
`Hilbert Ax₂`. -/
lemma subset_of_provable_axioms (hs : Ax₁ ⊆ Hilbert Ax₂) : Hilbert Ax₁ ⊆ Hilbert Ax₂ := sorry

lemma subset_of_subset_axioms (h : Ax₁ ⊆ Ax₂) : Hilbert Ax₁ ⊆ Hilbert Ax₂ :=
  subset_of_provable_axioms fun _ hφ => axm'! (h hφ)

open Axiom

instance instHasAxiomM [Ax.HasM] : (Hilbert Ax).HasAxiomM := sorry

instance instHasAxiomC [Ax.HasC] : (Hilbert Ax).HasAxiomC := sorry

instance instHasAxiomN [Ax.HasN] : (Hilbert Ax).HasAxiomN := sorry

instance instHasAxiomK [Ax.HasK] : (Hilbert Ax).HasAxiomK := sorry

instance instHasAxiomT [Ax.HasT] : (Hilbert Ax).HasAxiomT := sorry

instance instHasAxiomB [Ax.HasB] : (Hilbert Ax).HasAxiomB := sorry

instance instHasAxiomD [Ax.HasD] : (Hilbert Ax).HasAxiomD := sorry

instance instHasAxiomP [Ax.HasP] : (Hilbert Ax).HasAxiomP := sorry

instance instHasAxiomFour [Ax.HasFour] : (Hilbert Ax).HasAxiomFour := sorry

instance instHasAxiomFive [Ax.HasFive] : (Hilbert Ax).HasAxiomFive := sorry

end Hilbert

end LO.Modal

end
