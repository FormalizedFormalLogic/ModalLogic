module

public import Neighborhood.Logic.Cl

/-!
# Modal closure conditions of a logic

Closure of a logic under the congruence rule `RE` and the monotonicity rule `RM`, possession of
the usual modal axiom schemes, and the bundles of these conditions that name the classical
non-normal modal logics between `E` and `ET5`.
-/

@[expose] public section

namespace LO.Modal

namespace Logic

variable {L : Logic} {φ ψ χ : Formula} {n : ℕ} {g : Axioms.Geach.Taple}

/-! ### Rules -/

/-- Closure of a logic under the congruence rule for `□`. -/
class HasRE (L : Logic) where
  re : ∀ {φ ψ : Formula}, L ⊢ φ 🡘 ψ → L ⊢ □φ 🡘 □ψ

/-- Closure of a logic under the monotonicity rule for `□`. -/
class HasRM (L : Logic) where
  rm : ∀ {φ ψ : Formula}, L ⊢ φ 🡒 ψ → L ⊢ □φ 🡒 □ψ

lemma re! [L.HasRE] : L ⊢ φ 🡘 ψ → L ⊢ □φ 🡘 □ψ := HasRE.re

lemma rm! [L.HasRM] : L ⊢ φ 🡒 ψ → L ⊢ □φ 🡒 □ψ := HasRM.rm

lemma multire! [L.HasRE] (h : L ⊢ φ 🡘 ψ) : L ⊢ □^[n]φ 🡘 □^[n]ψ := by
  induction n with
  | zero => simpa;
  | succ n ih => simpa using re! ih;

/-! ### Axiom schemes -/

/-- A logic containing the axiom scheme `K`. -/
class HasAxiomK (L : Logic) where
  K : ∀ (φ ψ : Formula), L ⊢ Axioms.K φ ψ

/-- A logic containing the axiom scheme `M`. -/
class HasAxiomM (L : Logic) where
  M : ∀ (φ ψ : Formula), L ⊢ Axioms.M φ ψ

/-- A logic containing the axiom scheme `C`. -/
class HasAxiomC (L : Logic) where
  C : ∀ (φ ψ : Formula), L ⊢ Axioms.C φ ψ

/-- A logic containing the axiom `N`. -/
class HasAxiomN (L : Logic) where
  N : L ⊢ Axioms.N

/-- A logic containing the axiom scheme `T`. -/
class HasAxiomT (L : Logic) where
  T : ∀ (φ : Formula), L ⊢ Axioms.T φ

/-- A logic containing the axiom scheme `B`. -/
class HasAxiomB (L : Logic) where
  B : ∀ (φ : Formula), L ⊢ Axioms.B φ

/-- A logic containing the axiom scheme `D`. -/
class HasAxiomD (L : Logic) where
  D : ∀ (φ : Formula), L ⊢ Axioms.D φ

/-- A logic containing the axiom `P`. -/
class HasAxiomP (L : Logic) where
  P : L ⊢ Axioms.P

/-- A logic containing the axiom scheme `Four`. -/
class HasAxiomFour (L : Logic) where
  Four : ∀ (φ : Formula), L ⊢ Axioms.Four φ

/-- A logic containing the axiom scheme `Five`. -/
class HasAxiomFive (L : Logic) where
  Five : ∀ (φ : Formula), L ⊢ Axioms.Five φ

/-- A logic containing the Geach axiom scheme with parameters `g`. -/
class HasAxiomGeach (g : Axioms.Geach.Taple) (L : Logic) where
  Geach : ∀ (φ : Formula), L ⊢ Axioms.Geach g φ

@[simp] lemma axiomK! [L.HasAxiomK] : L ⊢ □(φ 🡒 ψ) 🡒 □φ 🡒 □ψ := HasAxiomK.K ..
@[simp] lemma axiomM! [L.HasAxiomM] : L ⊢ □(φ ⋏ ψ) 🡒 (□φ ⋏ □ψ) := HasAxiomM.M ..
@[simp] lemma axiomC! [L.HasAxiomC] : L ⊢ (□φ ⋏ □ψ) 🡒 □(φ ⋏ ψ) := HasAxiomC.C ..
@[simp] lemma axiomN! [L.HasAxiomN] : L ⊢ □(⊤ : Formula) := HasAxiomN.N
@[simp] lemma axiomT! [L.HasAxiomT] : L ⊢ □φ 🡒 φ := HasAxiomT.T ..
@[simp] lemma axiomB! [L.HasAxiomB] : L ⊢ φ 🡒 □◇φ := HasAxiomB.B ..
@[simp] lemma axiomD! [L.HasAxiomD] : L ⊢ □φ 🡒 ◇φ := HasAxiomD.D ..
@[simp] lemma axiomP! [L.HasAxiomP] : L ⊢ ∼□(⊥ : Formula) := HasAxiomP.P
@[simp] lemma axiomFour! [L.HasAxiomFour] : L ⊢ □φ 🡒 □□φ := HasAxiomFour.Four ..
@[simp] lemma axiomFive! [L.HasAxiomFive] : L ⊢ ◇φ 🡒 □◇φ := HasAxiomFive.Five ..

@[simp]
lemma axiomGeach! [L.HasAxiomGeach g] : L ⊢ ◇^[g.i](□^[g.m]φ) 🡒 □^[g.j](◇^[g.n]φ) :=
  HasAxiomGeach.Geach ..

section

variable [L.Cl]

@[simp] lemma axiomK'! [L.HasAxiomK] (h : L ⊢ □(φ 🡒 ψ)) : L ⊢ □φ 🡒 □ψ := axiomK! ⨀ h
@[simp] lemma axiomK''! [L.HasAxiomK] (h₁ : L ⊢ □(φ 🡒 ψ)) (h₂ : L ⊢ □φ) : L ⊢ □ψ := axiomK'! h₁ ⨀ h₂
lemma axiomM'! [L.HasAxiomM] (h : L ⊢ □(φ ⋏ ψ)) : L ⊢ □φ ⋏ □ψ := axiomM! ⨀ h
lemma axiomC'! [L.HasAxiomC] (h : L ⊢ □φ ⋏ □ψ) : L ⊢ □(φ ⋏ ψ) := axiomC! ⨀ h
@[simp] lemma axiomT'! [L.HasAxiomT] (h : L ⊢ □φ) : L ⊢ φ := axiomT! ⨀ h
lemma axiomD'! [L.HasAxiomD] (h : L ⊢ □φ) : L ⊢ ◇φ := axiomD! ⨀ h
@[simp] lemma axiomB'! [L.HasAxiomB] (h : L ⊢ φ) : L ⊢ □◇φ := axiomB! ⨀ h

instance [L.HasAxiomT] : L.HasAxiomGeach ⟨0, 0, 1, 0⟩ := ⟨fun _ => axiomT!⟩
instance [L.HasAxiomB] : L.HasAxiomGeach ⟨0, 1, 0, 1⟩ := ⟨fun _ => axiomB!⟩
instance [L.HasAxiomD] : L.HasAxiomGeach ⟨0, 0, 1, 1⟩ := ⟨fun _ => axiomD!⟩
instance [L.HasAxiomFour] : L.HasAxiomGeach ⟨0, 2, 1, 0⟩ := ⟨fun _ => axiomFour!⟩
instance [L.HasAxiomFive] : L.HasAxiomGeach ⟨1, 1, 0, 1⟩ := ⟨fun _ => axiomFive!⟩

end

/-! ### Bundles -/

/-- The closure conditions of the logic `E`. -/
class IsE (L : Logic) extends L.Cl, L.HasRE

class IsEM (L : Logic) extends L.IsE, L.HasAxiomM
class IsEC (L : Logic) extends L.IsE, L.HasAxiomC
class IsEN (L : Logic) extends L.IsE, L.HasAxiomN

class IsEMC (L : Logic) extends L.IsE, L.HasAxiomM, L.HasAxiomC
instance [L.IsEMC] : L.IsEM where
instance [L.IsEMC] : L.IsEC where

class IsEMN (L : Logic) extends L.IsE, L.HasAxiomM, L.HasAxiomN
instance [L.IsEMN] : L.IsEM where
instance [L.IsEMN] : L.IsEN where

class IsECN (L : Logic) extends L.IsE, L.HasAxiomC, L.HasAxiomN
instance [L.IsECN] : L.IsEC where
instance [L.IsECN] : L.IsEN where

class IsEMCN (L : Logic) extends L.IsE, L.HasAxiomM, L.HasAxiomC, L.HasAxiomN
instance [L.IsEMCN] : L.IsEMC where
instance [L.IsEMCN] : L.IsEMN where
instance [L.IsEMCN] : L.IsECN where

class IsEK (L : Logic) extends L.IsE, L.HasAxiomK

class IsEMK (L : Logic) extends L.IsEM, L.HasAxiomK
instance [L.IsEMK] : L.IsEK where

class IsET (L : Logic) extends L.IsE, L.HasAxiomT

class IsEMT (L : Logic) extends L.IsE, L.HasAxiomM, L.HasAxiomT
instance [L.IsEMT] : L.IsEM where
instance [L.IsEMT] : L.IsET where

class IsED (L : Logic) extends L.IsE, L.HasAxiomD

class IsEB (L : Logic) extends L.IsE, L.HasAxiomB

class IsETB (L : Logic) extends L.IsE, L.HasAxiomT, L.HasAxiomB
instance [L.IsETB] : L.IsET where
instance [L.IsETB] : L.IsEB where

class IsEND (L : Logic) extends L.IsEN, L.HasAxiomD
instance [L.IsEND] : L.IsED where

class IsE4 (L : Logic) extends L.IsE, L.HasAxiomFour

class IsEMC4 (L : Logic) extends L.IsEMC, L.HasAxiomFour
instance [L.IsEMC4] : L.IsE4 where

class IsEMT4 (L : Logic) extends L.IsE4, L.HasAxiomT, L.HasAxiomM
instance [L.IsEMT4] : L.IsEMT where

class IsE5 (L : Logic) extends L.IsE, L.HasAxiomFive

class IsET5 (L : Logic) extends L.IsE, L.HasAxiomT, L.HasAxiomFive
instance [L.IsET5] : L.IsET where
instance [L.IsET5] : L.IsE5 where

/-! ### Monotonicity rule and the axiom `M` -/

instance [L.IsEM] : L.HasRM := ⟨by
  intro φ ψ h;
  have h₁ : L ⊢ □φ 🡒 □(φ ⋏ ψ) := C_of_E_mp! <| re! <| E!_intro (CK!_of_C!_of_C! C!_id h) and₁!;
  exact C!_trans (C!_trans h₁ axiomM!) and₂!;⟩

instance [L.IsE] [L.HasRM] : L.IsEM where
  M _ _ := CK!_of_C!_of_C! (rm! and₁!) (rm! and₂!)

end Logic

end LO.Modal

end
