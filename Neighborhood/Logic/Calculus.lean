module

public import Neighborhood.Logic.Cl

/-!
# Modal closure conditions of a logic

Closure of a logic under the congruence rule `RE`, possession of the usual modal axiom schemes,
and the derived monotonicity rule `RM`.
-/

@[expose] public section

namespace Logic

variable {α : Type u} {L : Logic α} {A B C : Formula α} {n : ℕ} {g : Axioms.Geach.Taple}

/-! ### Rules -/

/-- Closure of a logic under the congruence rule for `□`. -/
class HasRE (L : Logic α) where
  re : ∀ {A B : Formula α}, A 🡘 B ∈ L → □A 🡘 □B ∈ L

lemma re! [L.HasRE] : A 🡘 B ∈ L → □A 🡘 □B ∈ L := HasRE.re

lemma multire! [L.HasRE] (h : A 🡘 B ∈ L) : □^[n]A 🡘 □^[n]B ∈ L := by
  induction n with
  | zero => simpa;
  | succ n ih => simpa using re! ih;

/-! ### Axiom schemes -/

/-- A logic containing the axiom scheme `K`. -/
class HasAxiomK (L : Logic α) where
  K : ∀ (A B : Formula α), Axioms.K A B ∈ L

/-- A logic containing the axiom scheme `M`. -/
class HasAxiomM (L : Logic α) where
  M : ∀ (A B : Formula α), Axioms.M A B ∈ L

/-- A logic containing the axiom scheme `C`. -/
class HasAxiomC (L : Logic α) where
  C : ∀ (A B : Formula α), Axioms.C A B ∈ L

/-- A logic containing the axiom `N`. -/
class HasAxiomN (L : Logic α) where
  N : Axioms.N ∈ L

/-- A logic containing the axiom scheme `T`. -/
class HasAxiomT (L : Logic α) where
  T : ∀ (A : Formula α), Axioms.T A ∈ L

/-- A logic containing the axiom scheme `B`. -/
class HasAxiomB (L : Logic α) where
  B : ∀ (A : Formula α), Axioms.B A ∈ L

/-- A logic containing the axiom scheme `D`. -/
class HasAxiomD (L : Logic α) where
  D : ∀ (A : Formula α), Axioms.D A ∈ L

/-- A logic containing the axiom `P`. -/
class HasAxiomP (L : Logic α) where
  P : Axioms.P ∈ L

/-- A logic containing the axiom scheme `Four`. -/
class HasAxiomFour (L : Logic α) where
  Four : ∀ (A : Formula α), Axioms.Four A ∈ L

/-- A logic containing the axiom scheme `Five`. -/
class HasAxiomFive (L : Logic α) where
  Five : ∀ (A : Formula α), Axioms.Five A ∈ L

/-- A logic containing the Geach axiom scheme with parameters `g`. -/
class HasAxiomGeach (g : Axioms.Geach.Taple) (L : Logic α) where
  Geach : ∀ (A : Formula α), Axioms.Geach g A ∈ L

@[simp] lemma axiomK! [L.HasAxiomK] : □(A 🡒 B) 🡒 □A 🡒 □B ∈ L := HasAxiomK.K ..
@[simp] lemma axiomM! [L.HasAxiomM] : □(A ⋏ B) 🡒 (□A ⋏ □B) ∈ L := HasAxiomM.M ..
@[simp] lemma axiomC! [L.HasAxiomC] : (□A ⋏ □B) 🡒 □(A ⋏ B) ∈ L := HasAxiomC.C ..
@[simp] lemma axiomN! [L.HasAxiomN] : □(⊤ : Formula α) ∈ L := HasAxiomN.N
@[simp] lemma axiomT! [L.HasAxiomT] : □A 🡒 A ∈ L := HasAxiomT.T ..
@[simp] lemma axiomB! [L.HasAxiomB] : A 🡒 □◇A ∈ L := HasAxiomB.B ..
@[simp] lemma axiomD! [L.HasAxiomD] : □A 🡒 ◇A ∈ L := HasAxiomD.D ..
@[simp] lemma axiomP! [L.HasAxiomP] : ∼□(⊥ : Formula α) ∈ L := HasAxiomP.P
@[simp] lemma axiomFour! [L.HasAxiomFour] : □A 🡒 □□A ∈ L := HasAxiomFour.Four ..
@[simp] lemma axiomFive! [L.HasAxiomFive] : ◇A 🡒 □◇A ∈ L := HasAxiomFive.Five ..

@[simp]
lemma axiomGeach! [L.HasAxiomGeach g] : ◇^[g.i](□^[g.m]A) 🡒 □^[g.j](◇^[g.n]A) ∈ L :=
  HasAxiomGeach.Geach ..

instance [L.HasAxiomT] : L.HasAxiomGeach ⟨0, 0, 1, 0⟩ := ⟨fun _ => axiomT!⟩
instance [L.HasAxiomB] : L.HasAxiomGeach ⟨0, 1, 0, 1⟩ := ⟨fun _ => axiomB!⟩
instance [L.HasAxiomD] : L.HasAxiomGeach ⟨0, 0, 1, 1⟩ := ⟨fun _ => axiomD!⟩
instance [L.HasAxiomFour] : L.HasAxiomGeach ⟨0, 2, 1, 0⟩ := ⟨fun _ => axiomFour!⟩
instance [L.HasAxiomFive] : L.HasAxiomGeach ⟨1, 1, 0, 1⟩ := ⟨fun _ => axiomFive!⟩

section

variable [L.Cl]

@[simp] lemma axiomK'! [L.HasAxiomK] (h : □(A 🡒 B) ∈ L) : □A 🡒 □B ∈ L := axiomK! ⨀ h
@[simp] lemma axiomK''! [L.HasAxiomK] (h₁ : □(A 🡒 B) ∈ L) (h₂ : □A ∈ L) : □B ∈ L := axiomK'! h₁ ⨀ h₂
lemma axiomM'! [L.HasAxiomM] (h : □(A ⋏ B) ∈ L) : □A ⋏ □B ∈ L := axiomM! ⨀ h
lemma axiomC'! [L.HasAxiomC] (h : □A ⋏ □B ∈ L) : □(A ⋏ B) ∈ L := axiomC! ⨀ h
@[simp] lemma axiomT'! [L.HasAxiomT] (h : □A ∈ L) : A ∈ L := axiomT! ⨀ h
lemma axiomD'! [L.HasAxiomD] (h : □A ∈ L) : ◇A ∈ L := axiomD! ⨀ h
@[simp] lemma axiomB'! [L.HasAxiomB] (h : A ∈ L) : □◇A ∈ L := axiomB! ⨀ h

/-! ### The monotonicity rule -/

/-- The monotonicity rule for `□`, derived from `RE` and the axiom scheme `M`. -/
lemma rm! [L.HasRE] [L.HasAxiomM] (h : A 🡒 B ∈ L) : □A 🡒 □B ∈ L := by
  have h₁ : □A 🡒 □(A ⋏ B) ∈ L :=
    C_of_E_mp! <| re! <| E!_intro (CK!_of_C!_of_C! C!_id h) and₁!;
  exact C!_trans (C!_trans h₁ axiomM!) and₂!;

/-! ### Derived axiom schemes -/

section

variable [L.HasRE]

/-- The axiom scheme `C` is derivable from `M` and `K`. -/
instance [L.HasAxiomM] [L.HasAxiomK] : L.HasAxiomC := ⟨by
  intro A B;
  have h₁ : □A 🡒 □(B 🡒 A) ∈ L := rm! implyK!;
  have h₂ : □(B 🡒 A) 🡒 □(B 🡒 A ⋏ B) ∈ L :=
    C_of_E_mp! <| re! <| E!_intro
      (CK!_iff_CC!.mp <| CK!_of_C!_of_C! (mdp₁! and₁! and₂!) and₂!)
      (CCC!_of_C!_right and₁!);
  exact mdp₁! (C!_trans (C!_trans and₁! (C!_trans h₁ h₂)) axiomK!) and₂!;⟩

/-- The axiom scheme `K` is derivable from `M` and `C`. -/
lemma axiomK!_of_MC [L.HasAxiomM] [L.HasAxiomC] : □(A 🡒 B) 🡒 □A 🡒 □B ∈ L :=
  CK!_iff_CC!.mp <| C!_trans axiomC! <| rm! <| mdp₁! and₁! and₂!

variable [L.HasAxiomT]

omit [L.HasRE] in
/-- The dual of the axiom scheme `T`. -/
lemma diaTc! : A 🡒 ◇A ∈ L := C!_trans dni! (contra! axiomT!)

/-- The necessitation rule, derived from `RE` and the axiom schemes `T` and `B`. -/
lemma nec! [L.HasAxiomB] (h : A ∈ L) : □A ∈ L :=
  C_of_E_mpr! (re! <| E!_intro diaTc! (C!_of_conseq! h)) ⨀ (axiomB! ⨀ h)

/-- The axiom `N` is derivable from `T` and `B`. -/
instance [L.HasAxiomB] : L.HasAxiomN := ⟨nec! verum!⟩

end

end

end Logic

end
