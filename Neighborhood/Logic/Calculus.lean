module

public import Neighborhood.Logic.Cl

/-!
# Modal closure conditions of a logic

Closure of a logic under the congruence rule `RE`, possession of the usual modal axiom schemes,
and the derived monotonicity rule `RM`.
-/

@[expose] public section

namespace Logic

variable {L : Logic} {φ ψ χ : Formula} {n : ℕ} {g : Axioms.Geach.Taple}

/-! ### Rules -/

/-- Closure of a logic under the congruence rule for `□`. -/
class HasRE (L : Logic) where
  re : ∀ {φ ψ : Formula}, φ 🡘 ψ ∈ L → □φ 🡘 □ψ ∈ L

lemma re! [L.HasRE] : φ 🡘 ψ ∈ L → □φ 🡘 □ψ ∈ L := HasRE.re

lemma multire! [L.HasRE] (h : φ 🡘 ψ ∈ L) : □^[n]φ 🡘 □^[n]ψ ∈ L := by
  induction n with
  | zero => simpa;
  | succ n ih => simpa using re! ih;

/-! ### Axiom schemes -/

/-- A logic containing the axiom scheme `K`. -/
class HasAxiomK (L : Logic) where
  K : ∀ (φ ψ : Formula), Axioms.K φ ψ ∈ L

/-- A logic containing the axiom scheme `M`. -/
class HasAxiomM (L : Logic) where
  M : ∀ (φ ψ : Formula), Axioms.M φ ψ ∈ L

/-- A logic containing the axiom scheme `C`. -/
class HasAxiomC (L : Logic) where
  C : ∀ (φ ψ : Formula), Axioms.C φ ψ ∈ L

/-- A logic containing the axiom `N`. -/
class HasAxiomN (L : Logic) where
  N : Axioms.N ∈ L

/-- A logic containing the axiom scheme `T`. -/
class HasAxiomT (L : Logic) where
  T : ∀ (φ : Formula), Axioms.T φ ∈ L

/-- A logic containing the axiom scheme `B`. -/
class HasAxiomB (L : Logic) where
  B : ∀ (φ : Formula), Axioms.B φ ∈ L

/-- A logic containing the axiom scheme `D`. -/
class HasAxiomD (L : Logic) where
  D : ∀ (φ : Formula), Axioms.D φ ∈ L

/-- A logic containing the axiom `P`. -/
class HasAxiomP (L : Logic) where
  P : Axioms.P ∈ L

/-- A logic containing the axiom scheme `Four`. -/
class HasAxiomFour (L : Logic) where
  Four : ∀ (φ : Formula), Axioms.Four φ ∈ L

/-- A logic containing the axiom scheme `Five`. -/
class HasAxiomFive (L : Logic) where
  Five : ∀ (φ : Formula), Axioms.Five φ ∈ L

/-- A logic containing the Geach axiom scheme with parameters `g`. -/
class HasAxiomGeach (g : Axioms.Geach.Taple) (L : Logic) where
  Geach : ∀ (φ : Formula), Axioms.Geach g φ ∈ L

@[simp] lemma axiomK! [L.HasAxiomK] : □(φ 🡒 ψ) 🡒 □φ 🡒 □ψ ∈ L := HasAxiomK.K ..
@[simp] lemma axiomM! [L.HasAxiomM] : □(φ ⋏ ψ) 🡒 (□φ ⋏ □ψ) ∈ L := HasAxiomM.M ..
@[simp] lemma axiomC! [L.HasAxiomC] : (□φ ⋏ □ψ) 🡒 □(φ ⋏ ψ) ∈ L := HasAxiomC.C ..
@[simp] lemma axiomN! [L.HasAxiomN] : □(⊤ : Formula) ∈ L := HasAxiomN.N
@[simp] lemma axiomT! [L.HasAxiomT] : □φ 🡒 φ ∈ L := HasAxiomT.T ..
@[simp] lemma axiomB! [L.HasAxiomB] : φ 🡒 □◇φ ∈ L := HasAxiomB.B ..
@[simp] lemma axiomD! [L.HasAxiomD] : □φ 🡒 ◇φ ∈ L := HasAxiomD.D ..
@[simp] lemma axiomP! [L.HasAxiomP] : ∼□(⊥ : Formula) ∈ L := HasAxiomP.P
@[simp] lemma axiomFour! [L.HasAxiomFour] : □φ 🡒 □□φ ∈ L := HasAxiomFour.Four ..
@[simp] lemma axiomFive! [L.HasAxiomFive] : ◇φ 🡒 □◇φ ∈ L := HasAxiomFive.Five ..

@[simp]
lemma axiomGeach! [L.HasAxiomGeach g] : ◇^[g.i](□^[g.m]φ) 🡒 □^[g.j](◇^[g.n]φ) ∈ L :=
  HasAxiomGeach.Geach ..

instance [L.HasAxiomT] : L.HasAxiomGeach ⟨0, 0, 1, 0⟩ := ⟨fun _ => axiomT!⟩
instance [L.HasAxiomB] : L.HasAxiomGeach ⟨0, 1, 0, 1⟩ := ⟨fun _ => axiomB!⟩
instance [L.HasAxiomD] : L.HasAxiomGeach ⟨0, 0, 1, 1⟩ := ⟨fun _ => axiomD!⟩
instance [L.HasAxiomFour] : L.HasAxiomGeach ⟨0, 2, 1, 0⟩ := ⟨fun _ => axiomFour!⟩
instance [L.HasAxiomFive] : L.HasAxiomGeach ⟨1, 1, 0, 1⟩ := ⟨fun _ => axiomFive!⟩

section

variable [L.Cl]

@[simp] lemma axiomK'! [L.HasAxiomK] (h : □(φ 🡒 ψ) ∈ L) : □φ 🡒 □ψ ∈ L := axiomK! ⨀ h
@[simp] lemma axiomK''! [L.HasAxiomK] (h₁ : □(φ 🡒 ψ) ∈ L) (h₂ : □φ ∈ L) : □ψ ∈ L := axiomK'! h₁ ⨀ h₂
lemma axiomM'! [L.HasAxiomM] (h : □(φ ⋏ ψ) ∈ L) : □φ ⋏ □ψ ∈ L := axiomM! ⨀ h
lemma axiomC'! [L.HasAxiomC] (h : □φ ⋏ □ψ ∈ L) : □(φ ⋏ ψ) ∈ L := axiomC! ⨀ h
@[simp] lemma axiomT'! [L.HasAxiomT] (h : □φ ∈ L) : φ ∈ L := axiomT! ⨀ h
lemma axiomD'! [L.HasAxiomD] (h : □φ ∈ L) : ◇φ ∈ L := axiomD! ⨀ h
@[simp] lemma axiomB'! [L.HasAxiomB] (h : φ ∈ L) : □◇φ ∈ L := axiomB! ⨀ h

/-! ### The monotonicity rule -/

/-- The monotonicity rule for `□`, derived from `RE` and the axiom scheme `M`. -/
lemma rm! [L.HasRE] [L.HasAxiomM] (h : φ 🡒 ψ ∈ L) : □φ 🡒 □ψ ∈ L := by
  have h₁ : □φ 🡒 □(φ ⋏ ψ) ∈ L :=
    C_of_E_mp! <| re! <| E!_intro (CK!_of_C!_of_C! C!_id h) and₁!;
  exact C!_trans (C!_trans h₁ axiomM!) and₂!;

/-! ### Derived axiom schemes -/

section

variable [L.HasRE]

/-- The axiom scheme `C` is derivable from `M` and `K`. -/
instance [L.HasAxiomM] [L.HasAxiomK] : L.HasAxiomC := ⟨by
  intro φ ψ;
  have h₁ : □φ 🡒 □(ψ 🡒 φ) ∈ L := rm! implyK!;
  have h₂ : □(ψ 🡒 φ) 🡒 □(ψ 🡒 φ ⋏ ψ) ∈ L :=
    C_of_E_mp! <| re! <| E!_intro
      (CK!_iff_CC!.mp <| CK!_of_C!_of_C! (mdp₁! and₁! and₂!) and₂!)
      (CCC!_of_C!_right and₁!);
  exact mdp₁! (C!_trans (C!_trans and₁! (C!_trans h₁ h₂)) axiomK!) and₂!;⟩

/-- The axiom scheme `K` is derivable from `M` and `C`. -/
lemma axiomK!_of_MC [L.HasAxiomM] [L.HasAxiomC] : □(φ 🡒 ψ) 🡒 □φ 🡒 □ψ ∈ L :=
  CK!_iff_CC!.mp <| C!_trans axiomC! <| rm! <| mdp₁! and₁! and₂!

variable [L.HasAxiomT]

omit [L.HasRE] in
/-- The dual of the axiom scheme `T`. -/
lemma diaTc! : φ 🡒 ◇φ ∈ L := C!_trans dni! (contra! axiomT!)

/-- The necessitation rule, derived from `RE` and the axiom schemes `T` and `B`. -/
lemma nec! [L.HasAxiomB] (h : φ ∈ L) : □φ ∈ L :=
  C_of_E_mpr! (re! <| E!_intro diaTc! (C!_of_conseq! h)) ⨀ (axiomB! ⨀ h)

/-- The axiom `N` is derivable from `T` and `B`. -/
instance [L.HasAxiomB] : L.HasAxiomN := ⟨nec! verum!⟩

end

end

end Logic

end
