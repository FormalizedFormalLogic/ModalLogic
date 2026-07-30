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

@[simp] lemma iff_mem : Hilbert Ax φ ↔ φ ∈ Hilbert Ax := Iff.rfl

@[grind ←] lemma axm! (s : Substitution) (h : φ ∈ Ax) : φ⟦s⟧ ∈ Hilbert Ax := axm s h

@[grind ←] lemma axm'! (h : φ ∈ Ax) : φ ∈ Hilbert Ax := by simpa using axm! .id h

/-- Provability in a Hilbert system is closed under substitution. -/
lemma subst_mem (h : φ ∈ Hilbert Ax) : φ⟦s⟧ ∈ Hilbert Ax := by
  induction h with
  | @axm _ s' hφ => simpa using axm (s := s'.comp s) hφ;
  | mdp _ _ ih₁ ih₂ => exact mdp ih₁ ih₂;
  | re _ ih => exact re ih;
  | _ => simp;

/-- Induction on a proof in a Hilbert system. -/
protected lemma rec! {motive : (φ : Formula) → φ ∈ Hilbert Ax → Prop}
    (axm : ∀ {φ} (s : Substitution), (h : φ ∈ Ax) → motive (φ⟦s⟧) (axm! s h))
    (mdp : ∀ {φ ψ}, {h₁ : φ 🡒 ψ ∈ Hilbert Ax} → {h₂ : φ ∈ Hilbert Ax} →
      motive (φ 🡒 ψ) h₁ → motive φ h₂ → motive ψ (h₁ ⨀ h₂))
    (re : ∀ {φ ψ}, {h : φ 🡘 ψ ∈ Hilbert Ax} → motive (φ 🡘 ψ) h → motive (□φ 🡘 □ψ) (re! h))
    (implyK : ∀ φ ψ, motive (Axioms.ImplyK φ ψ) (by simp))
    (implyS : ∀ φ ψ χ, motive (Axioms.ImplyS φ ψ χ) (by simp))
    (dne : ∀ φ, motive (Axioms.DNE φ) (by simp))
    (andElim₁ : ∀ φ ψ, motive (Axioms.AndElim₁ φ ψ) (by simp))
    (andElim₂ : ∀ φ ψ, motive (Axioms.AndElim₂ φ ψ) (by simp))
    (andIntro : ∀ φ ψ, motive (Axioms.AndIntro φ ψ) (by simp))
    (orIntro₁ : ∀ φ ψ, motive (Axioms.OrIntro₁ φ ψ) (by simp))
    (orIntro₂ : ∀ φ ψ, motive (Axioms.OrIntro₂ φ ψ) (by simp))
    (orElim : ∀ φ ψ χ, motive (Axioms.OrElim φ ψ χ) (by simp)) :
    ∀ {φ}, (h : φ ∈ Hilbert Ax) → motive φ h := by
  intro φ h;
  induction h with
  | axm s hφ => exact axm s hφ;
  | mdp _ _ ih₁ ih₂ => exact mdp ih₁ ih₂;
  | re _ ih => exact re ih;
  | implyK => apply implyK;
  | implyS => apply implyS;
  | dne => apply dne;
  | andElim₁ => apply andElim₁;
  | andElim₂ => apply andElim₂;
  | andIntro => apply andIntro;
  | orIntro₁ => apply orIntro₁;
  | orIntro₂ => apply orIntro₂;
  | orElim => apply orElim;

/-- If every scheme of `Ax₁` is provable in `Hilbert Ax₂`, then `Hilbert Ax₁` is contained in
`Hilbert Ax₂`. -/
lemma subset_of_provable_axioms (hs : Ax₁ ⊆ Hilbert Ax₂) : Hilbert Ax₁ ⊆ Hilbert Ax₂ := by
  intro φ h;
  induction h using Hilbert.rec! with
  | axm s hφ => exact subst_mem (hs hφ);
  | mdp ih₁ ih₂ => exact ih₁ ⨀ ih₂;
  | re ih => exact re! ih;
  | _ => simp;

lemma subset_of_subset_axioms (h : Ax₁ ⊆ Ax₂) : Hilbert Ax₁ ⊆ Hilbert Ax₂ :=
  subset_of_provable_axioms fun _ hφ => axm'! (h hφ)

open Axiom

instance instHasAxiomM [Ax.HasM] : (Hilbert Ax).HasAxiomM where
  M φ ψ := by
    have h := Hilbert.axm
      (φ := Axioms.M (.atom (HasM.p Ax)) (.atom (HasM.q Ax)))
      (s := fun b => if HasM.p Ax = b then φ else if HasM.q Ax = b then ψ else .atom b)
      HasM.mem_M;
    simpa [HasM.ne_pq] using h;

instance instHasAxiomC [Ax.HasC] : (Hilbert Ax).HasAxiomC where
  C φ ψ := by
    have h := Hilbert.axm
      (φ := Axioms.C (.atom (HasC.p Ax)) (.atom (HasC.q Ax)))
      (s := fun b => if HasC.p Ax = b then φ else if HasC.q Ax = b then ψ else .atom b)
      HasC.mem_C;
    simpa [HasC.ne_pq] using h;

instance instHasAxiomN [Ax.HasN] : (Hilbert Ax).HasAxiomN where
  N := by simpa using Hilbert.axm (φ := Axioms.N) (s := .id) HasN.mem_N

instance instHasAxiomK [Ax.HasK] : (Hilbert Ax).HasAxiomK where
  K φ ψ := by
    have h := Hilbert.axm
      (φ := Axioms.K (.atom (HasK.p Ax)) (.atom (HasK.q Ax)))
      (s := fun b => if HasK.p Ax = b then φ else if HasK.q Ax = b then ψ else .atom b)
      HasK.mem_K;
    simpa [HasK.ne_pq] using h;

instance instHasAxiomT [Ax.HasT] : (Hilbert Ax).HasAxiomT where
  T φ := by
    have h := Hilbert.axm
      (φ := Axioms.T (.atom (HasT.p Ax)))
      (s := fun b => if HasT.p Ax = b then φ else .atom b)
      HasT.mem_T;
    simpa using h;

instance instHasAxiomB [Ax.HasB] : (Hilbert Ax).HasAxiomB where
  B φ := by
    have h := Hilbert.axm
      (φ := Axioms.B (.atom (HasB.p Ax)))
      (s := fun b => if HasB.p Ax = b then φ else .atom b)
      HasB.mem_B;
    simpa using h;

instance instHasAxiomD [Ax.HasD] : (Hilbert Ax).HasAxiomD where
  D φ := by
    have h := Hilbert.axm
      (φ := Axioms.D (.atom (HasD.p Ax)))
      (s := fun b => if HasD.p Ax = b then φ else .atom b)
      HasD.mem_D;
    simpa using h;

instance instHasAxiomP [Ax.HasP] : (Hilbert Ax).HasAxiomP where
  P := by simpa using Hilbert.axm (φ := Axioms.P) (s := .id) HasP.mem_P

instance instHasAxiomFour [Ax.HasFour] : (Hilbert Ax).HasAxiomFour where
  Four φ := by
    have h := Hilbert.axm
      (φ := Axioms.Four (.atom (HasFour.p Ax)))
      (s := fun b => if HasFour.p Ax = b then φ else .atom b)
      HasFour.mem_Four;
    simpa using h;

instance instHasAxiomFive [Ax.HasFive] : (Hilbert Ax).HasAxiomFive where
  Five φ := by
    have h := Hilbert.axm
      (φ := Axioms.Five (.atom (HasFive.p Ax)))
      (s := fun b => if HasFive.p Ax = b then φ else .atom b)
      HasFive.mem_Five;
    simpa using h;

end Hilbert

end LO.Modal

end
