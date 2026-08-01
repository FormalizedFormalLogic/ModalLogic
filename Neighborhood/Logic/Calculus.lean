module

public import Neighborhood.Logic.Cl

/-!
# Modal closure conditions of a logic

Closure of a logic under the congruence rule `RE` and possession of the usual modal axiom
schemes, together with the rules (`RM`, necessitation) and the derivations among the axiom
schemes that follow from these closure conditions.
-/

@[expose] public section

namespace Logic

variable {α : Type u} {L : Logic α} {A B C : Formula α} {n : ℕ} {g : Axioms.Geach.Taple}

/-! ### The congruence rule -/

class HasRE (L : Logic α) where
  re : ∀ {A B : Formula α}, A 🡘 B ∈ L → □A 🡘 □B ∈ L

lemma re [L.HasRE] : A 🡘 B ∈ L → □A 🡘 □B ∈ L := HasRE.re

lemma multire [L.HasRE] (h : A 🡘 B ∈ L) : □^[n]A 🡘 □^[n]B ∈ L := by
  induction n with
  | zero => simpa;
  | succ n ih => simpa using re ih;

/-! ### Axiom schemes -/

class HasAxiomK (L : Logic α) where
  K : ∀ (A B : Formula α), Axioms.K A B ∈ L

class HasAxiomM (L : Logic α) where
  M : ∀ (A B : Formula α), Axioms.M A B ∈ L

class HasAxiomC (L : Logic α) where
  C : ∀ (A B : Formula α), Axioms.C A B ∈ L

class HasAxiomN (L : Logic α) where
  N : Axioms.N ∈ L

class HasAxiomT (L : Logic α) where
  T : ∀ (A : Formula α), Axioms.T A ∈ L

class HasAxiomB (L : Logic α) where
  B : ∀ (A : Formula α), Axioms.B A ∈ L

class HasAxiomD (L : Logic α) where
  D : ∀ (A : Formula α), Axioms.D A ∈ L

class HasAxiomP (L : Logic α) where
  P : Axioms.P ∈ L

class HasAxiomFour (L : Logic α) where
  Four : ∀ (A : Formula α), Axioms.Four A ∈ L

class HasAxiomFive (L : Logic α) where
  Five : ∀ (A : Formula α), Axioms.Five A ∈ L

class HasAxiomGeach (g : Axioms.Geach.Taple) (L : Logic α) where
  Geach : ∀ (A : Formula α), Axioms.Geach g A ∈ L

@[simp] lemma axiomK [L.HasAxiomK] : □(A 🡒 B) 🡒 □A 🡒 □B ∈ L := HasAxiomK.K ..
@[simp] lemma axiomM [L.HasAxiomM] : □(A ⋏ B) 🡒 (□A ⋏ □B) ∈ L := HasAxiomM.M ..
@[simp] lemma axiomC [L.HasAxiomC] : (□A ⋏ □B) 🡒 □(A ⋏ B) ∈ L := HasAxiomC.C ..
@[simp] lemma axiomN [L.HasAxiomN] : □⊤ ∈ L := HasAxiomN.N
@[simp] lemma axiomT [L.HasAxiomT] : □A 🡒 A ∈ L := HasAxiomT.T ..
@[simp] lemma axiomB [L.HasAxiomB] : A 🡒 □◇A ∈ L := HasAxiomB.B ..
@[simp] lemma axiomD [L.HasAxiomD] : □A 🡒 ◇A ∈ L := HasAxiomD.D ..
@[simp] lemma axiomP [L.HasAxiomP] : ∼□⊥ ∈ L := HasAxiomP.P
@[simp] lemma axiomFour [L.HasAxiomFour] : □A 🡒 □□A ∈ L := HasAxiomFour.Four ..
@[simp] lemma axiomFive [L.HasAxiomFive] : ◇A 🡒 □◇A ∈ L := HasAxiomFive.Five ..

@[simp]
lemma axiomGeach [L.HasAxiomGeach g] : ◇^[g.i](□^[g.m]A) 🡒 □^[g.j](◇^[g.n]A) ∈ L :=
  HasAxiomGeach.Geach ..

lemma axiomK_subset [L.HasAxiomK] : { Axioms.K A B | (A) (B) } ⊆ L := by
  rintro _ ⟨_, _, rfl⟩; exact axiomK
lemma axiomM_subset [L.HasAxiomM] : { Axioms.M A B | (A) (B) } ⊆ L := by
  rintro _ ⟨_, _, rfl⟩; exact axiomM
lemma axiomC_subset [L.HasAxiomC] : { Axioms.C A B | (A) (B) } ⊆ L := by
  rintro _ ⟨_, _, rfl⟩; exact axiomC
lemma axiomN_subset [L.HasAxiomN] : {Axioms.N} ⊆ L := by
  rintro _ rfl; exact axiomN
lemma axiomT_subset [L.HasAxiomT] : { Axioms.T A | (A) } ⊆ L := by
  rintro _ ⟨_, rfl⟩; exact axiomT
lemma axiomB_subset [L.HasAxiomB] : { Axioms.B A | (A) } ⊆ L := by
  rintro _ ⟨_, rfl⟩; exact axiomB
lemma axiomD_subset [L.HasAxiomD] : { Axioms.D A | (A) } ⊆ L := by
  rintro _ ⟨_, rfl⟩; exact axiomD
lemma axiomP_subset [L.HasAxiomP] : {Axioms.P} ⊆ L := by
  rintro _ rfl; exact axiomP
lemma axiomFour_subset [L.HasAxiomFour] : { Axioms.Four A | (A) } ⊆ L := by
  rintro _ ⟨_, rfl⟩; exact axiomFour
lemma axiomFive_subset [L.HasAxiomFive] : { Axioms.Five A | (A) } ⊆ L := by
  rintro _ ⟨_, rfl⟩; exact axiomFive

instance [L.HasAxiomT] : L.HasAxiomGeach ⟨0, 0, 1, 0⟩ := ⟨fun _ => axiomT⟩
instance [L.HasAxiomB] : L.HasAxiomGeach ⟨0, 1, 0, 1⟩ := ⟨fun _ => axiomB⟩
instance [L.HasAxiomD] : L.HasAxiomGeach ⟨0, 0, 1, 1⟩ := ⟨fun _ => axiomD⟩
instance [L.HasAxiomFour] : L.HasAxiomGeach ⟨0, 2, 1, 0⟩ := ⟨fun _ => axiomFour⟩
instance [L.HasAxiomFive] : L.HasAxiomGeach ⟨1, 1, 0, 1⟩ := ⟨fun _ => axiomFive⟩

section

variable [L.Cl]

/-! ### Modus ponens forms of the axiom schemes -/

@[simp] lemma axiomK' [L.HasAxiomK] (h : □(A 🡒 B) ∈ L) : □A 🡒 □B ∈ L := axiomK ⨀ h
@[simp] lemma axiomK'' [L.HasAxiomK] (h₁ : □(A 🡒 B) ∈ L) (h₂ : □A ∈ L) : □B ∈ L := axiomK' h₁ ⨀ h₂
lemma axiomM' [L.HasAxiomM] (h : □(A ⋏ B) ∈ L) : □A ⋏ □B ∈ L := axiomM ⨀ h
lemma axiomC' [L.HasAxiomC] (h : □A ⋏ □B ∈ L) : □(A ⋏ B) ∈ L := axiomC ⨀ h
@[simp] lemma axiomT' [L.HasAxiomT] (h : □A ∈ L) : A ∈ L := axiomT ⨀ h
lemma axiomD' [L.HasAxiomD] (h : □A ∈ L) : ◇A ∈ L := axiomD ⨀ h
@[simp] lemma axiomB' [L.HasAxiomB] (h : A ∈ L) : □◇A ∈ L := axiomB ⨀ h

/-! ### Duals of the axiom schemes -/

lemma EDiaNNBox [L.HasRE] : ◇(∼A) 🡘 ∼□A ∈ L := by
  have h₁ : ∼∼A 🡘 A ∈ L := E_intro dne dni;
  have h₂ : □(∼∼A) 🡘 □A ∈ L := re h₁;
  have h₃ : ◇(∼A) 🡒 ∼□A ∈ L := contra (C_of_E_mpr h₂);
  have h₄ : ∼□A 🡒 ◇(∼A) ∈ L := contra (C_of_E_mp h₂);
  exact E_intro h₃ h₄;

lemma diaTc [L.HasAxiomT] : A 🡒 ◇A ∈ L := by
  have h₁ : □(∼A) 🡒 ∼A ∈ L := axiomT;
  have h₂ : ∼∼A 🡒 ◇A ∈ L := contra h₁;
  exact C_trans dni h₂;

lemma CNBoxNBox [L.HasRE] [L.HasAxiomB] : ∼A 🡒 □(∼□A) ∈ L := by
  have h₁ : ∼A 🡒 □◇(∼A) ∈ L := axiomB;
  have h₂ : □◇(∼A) 🡘 □(∼□A) ∈ L := re EDiaNNBox;
  have h₃ : □◇(∼A) 🡒 □(∼□A) ∈ L := C_of_E_mp h₂;
  exact C_trans h₁ h₃;

lemma diaBc [L.HasRE] [L.HasAxiomB] : ◇□A 🡒 A ∈ L := by
  have h₁ : ∼A 🡒 □(∼□A) ∈ L := CNBoxNBox;
  have h₂ : ◇□A 🡒 ∼∼A ∈ L := contra h₁;
  exact C_trans h₂ dne;

lemma diaFourc [L.HasRE] [L.HasAxiomFour] : ◇◇A 🡒 ◇A ∈ L := by
  have h₁ : ∼◇A 🡘 □(∼A) ∈ L := E_intro dne dni;
  have h₂ : □(∼◇A) 🡘 □□(∼A) ∈ L := re h₁;
  have h₃ : □(∼A) 🡒 □(∼◇A) ∈ L := C_trans axiomFour (C_of_E_mpr h₂);
  exact contra h₃;

lemma CNBoxBoxNBox [L.HasRE] [L.HasAxiomFive] : ∼□A 🡒 □(∼□A) ∈ L := by
  have h₁ : ∼□A 🡒 ◇(∼A) ∈ L := C_of_E_mpr EDiaNNBox;
  have h₂ : ◇(∼A) 🡒 □◇(∼A) ∈ L := axiomFive;
  have h₃ : □◇(∼A) 🡘 □(∼□A) ∈ L := re EDiaNNBox;
  have h₄ : □◇(∼A) 🡒 □(∼□A) ∈ L := C_of_E_mp h₃;
  have h₅ : ◇(∼A) 🡒 □(∼□A) ∈ L := C_trans h₂ h₄;
  exact C_trans h₁ h₅;

lemma diaFivec [L.HasRE] [L.HasAxiomFive] : ◇□A 🡒 □A ∈ L := by
  have h₁ : ∼□A 🡒 □(∼□A) ∈ L := CNBoxBoxNBox;
  have h₂ : ◇□A 🡒 ∼∼□A ∈ L := contra h₁;
  exact C_trans h₂ dne;

/-! ### Derived rules -/

lemma rm [L.HasRE] [L.HasAxiomM] (h : A 🡒 B ∈ L) : □A 🡒 □B ∈ L := by
  have h₁ : A 🡒 A ⋏ B ∈ L := CK_of_C_of_C C_id h;
  have h₂ : A 🡘 A ⋏ B ∈ L := E_intro h₁ and₁;
  have h₃ : □A 🡘 □(A ⋏ B) ∈ L := re h₂;
  have h₄ : □A 🡒 □(A ⋏ B) ∈ L := C_of_E_mp h₃;
  have h₅ : □A 🡒 (□A ⋏ □B) ∈ L := C_trans h₄ axiomM;
  exact C_trans h₅ and₂;

lemma rmDia [L.HasRE] [L.HasAxiomM] (h : A 🡒 B ∈ L) : ◇A 🡒 ◇B ∈ L := by
  have h₁ : ∼B 🡒 ∼A ∈ L := contra h;
  have h₂ : □(∼B) 🡒 □(∼A) ∈ L := rm h₁;
  exact contra h₂;

lemma nec [L.HasRE] [L.HasAxiomT] [L.HasAxiomB] (h : A ∈ L) : □A ∈ L := by
  have h₁ : A 🡘 ◇A ∈ L := E_intro diaTc (C_of_conseq h);
  have h₂ : □A 🡘 □◇A ∈ L := re h₁;
  have h₃ : □◇A 🡒 □A ∈ L := C_of_E_mpr h₂;
  have h₄ : □◇A ∈ L := axiomB ⨀ h;
  exact h₃ ⨀ h₄;

/-! ### Derived axiom schemes -/

section

variable [L.HasRE]

/-! #### The axiom scheme `M` -/

private lemma rm_of_KN [L.HasAxiomK] [L.HasAxiomN] (h : A 🡒 B ∈ L) : □A 🡒 □B ∈ L := by
  have h₁ : (A 🡒 B) 🡘 ⊤ ∈ L := E_intro (C_of_conseq verum) (C_of_conseq h);
  have h₂ : □(A 🡒 B) 🡘 □⊤ ∈ L := re h₁;
  have h₃ : □⊤ 🡒 □(A 🡒 B) ∈ L := C_of_E_mpr h₂;
  have h₄ : □(A 🡒 B) ∈ L := h₃ ⨀ axiomN;
  exact axiomK' h₄;

instance [L.HasAxiomK] [L.HasAxiomN] : L.HasAxiomM := by
  constructor;
  intro A B;
  have h₁ : □(A ⋏ B) 🡒 □A ∈ L := rm_of_KN and₁;
  have h₂ : □(A ⋏ B) 🡒 □B ∈ L := rm_of_KN and₂;
  exact CK_of_C_of_C h₁ h₂;

/-! #### The axiom scheme `C` -/

instance [L.HasAxiomM] [L.HasAxiomK] : L.HasAxiomC := by
  constructor;
  intro A B;
  have h₁ : □A 🡒 □(B 🡒 A ⋏ B) ∈ L := rm and₃;
  have h₂ : □(B 🡒 A ⋏ B) 🡒 (□B 🡒 □(A ⋏ B)) ∈ L := axiomK;
  have h₃ : □A 🡒 (□B 🡒 □(A ⋏ B)) ∈ L := C_trans h₁ h₂;
  have h₄ : (□A ⋏ □B) 🡒 (□B 🡒 □(A ⋏ B)) ∈ L := C_trans and₁ h₃;
  exact mdp₁ h₄ and₂;

instance [L.HasAxiomM] [L.HasAxiomB] : L.HasAxiomC := by
  constructor;
  intro A B;
  have h₁ : (□A ⋏ □B) 🡒 □◇(□A ⋏ □B) ∈ L := axiomB;
  have h₂ : ◇(□A ⋏ □B) 🡒 A ∈ L := C_trans (rmDia and₁) diaBc;
  have h₃ : ◇(□A ⋏ □B) 🡒 B ∈ L := C_trans (rmDia and₂) diaBc;
  have h₄ : ◇(□A ⋏ □B) 🡒 (A ⋏ B) ∈ L := CK_of_C_of_C h₂ h₃;
  have h₅ : □◇(□A ⋏ □B) 🡒 □(A ⋏ B) ∈ L := rm h₄;
  exact C_trans h₁ h₅;

/-! #### The axiom scheme `K` -/

instance [L.HasAxiomM] [L.HasAxiomC] : L.HasAxiomK := by
  constructor;
  intro A B;
  have h₁ : ((A 🡒 B) ⋏ A) 🡒 B ∈ L := mdp₁ and₁ and₂;
  have h₂ : □((A 🡒 B) ⋏ A) 🡒 □B ∈ L := rm h₁;
  have h₃ : (□(A 🡒 B) ⋏ □A) 🡒 □((A 🡒 B) ⋏ A) ∈ L := axiomC;
  have h₄ : (□(A 🡒 B) ⋏ □A) 🡒 □B ∈ L := C_trans h₃ h₂;
  exact CK_iff_CC.mp h₄;

/-! #### The axiom `N` -/

private lemma axiomN_of_box (h : A ∈ L) (hb : □A ∈ L) : Axioms.N ∈ L := by
  have h₁ : A 🡘 ⊤ ∈ L := E_intro (C_of_conseq verum) (C_of_conseq h);
  have h₂ : □A 🡘 □⊤ ∈ L := re h₁;
  exact C_of_E_mp h₂ ⨀ hb;

private lemma diaTop_of_P [L.HasAxiomP] : ◇⊤ ∈ L := by
  have h₁ : ∼⊤ 🡒 ⊥ ∈ L := mdp₁ C_id (C_of_conseq verum);
  have h₂ : ⊥ 🡒 ∼⊤ ∈ L := efq;
  have h₃ : ∼⊤ 🡘 ⊥ ∈ L := E_intro h₁ h₂;
  have h₄ : □(∼⊤) 🡘 □⊥ ∈ L := re h₃;
  have h₅ : □(∼⊤) 🡒 □⊥ ∈ L := C_of_E_mp h₄;
  exact C_trans h₅ axiomP;

instance [L.HasAxiomM] [L.HasAxiomB] : L.HasAxiomN := by
  constructor;
  have h₁ : ◇⊤ 🡒 ⊤ ∈ L := C_of_conseq verum;
  have h₂ : □◇⊤ 🡒 □⊤ ∈ L := rm h₁;
  have h₃ : □◇⊤ ∈ L := axiomB' verum;
  exact h₂ ⨀ h₃;

instance [L.HasAxiomM] [L.HasAxiomFive] : L.HasAxiomN := by
  constructor;
  have h₁ : ∼⊤ 🡒 ⊤ 🡒 ◇⊤ ∈ L := CNC;
  have h₂ : ∼⊤ 🡒 ⊤ ∈ L := C_of_conseq verum;
  have h₃ : ∼⊤ 🡒 ◇⊤ ∈ L := mdp₁ h₁ h₂;
  have h₄ : □(∼⊤) 🡒 □◇⊤ ∈ L := rm h₃;
  have h₅ : ◇⊤ 🡒 □◇⊤ ∈ L := axiomFive;
  have h₆ : □◇⊤ ∈ L := of_C_of_C_of_A h₄ h₅ lem;
  have h₇ : ◇⊤ 🡒 ⊤ ∈ L := C_of_conseq verum;
  have h₈ : □◇⊤ 🡒 □⊤ ∈ L := rm h₇;
  exact h₈ ⨀ h₆;

instance [L.HasAxiomP] [L.HasAxiomB] : L.HasAxiomN := by
  constructor;
  have h₁ : ◇⊤ ∈ L := diaTop_of_P;
  have h₂ : □◇⊤ ∈ L := axiomB' verum;
  exact axiomN_of_box h₁ h₂;

instance [L.HasAxiomP] [L.HasAxiomFive] : L.HasAxiomN := by
  constructor;
  have h₁ : ◇⊤ ∈ L := diaTop_of_P;
  have h₂ : □◇⊤ ∈ L := axiomFive ⨀ h₁;
  exact axiomN_of_box h₁ h₂;

instance [L.HasAxiomD] [L.HasAxiomB] [L.HasAxiomFive] : L.HasAxiomN := by
  constructor;
  have h₁ : □◇⊤ ∈ L := axiomB' verum;
  have h₂ : ◇◇⊤ ∈ L := axiomD ⨀ h₁;
  have h₃ : □◇◇⊤ ∈ L := axiomFive ⨀ h₂;
  exact axiomN_of_box h₂ h₃;

instance [L.HasAxiomB] [L.HasAxiomFour] : L.HasAxiomN := by
  constructor;
  have h₁ : □◇⊤ ∈ L := axiomB' verum;
  have h₂ : □□◇⊤ ∈ L := axiomFour ⨀ h₁;
  exact axiomN_of_box h₁ h₂;

instance [L.HasAxiomT] [L.HasAxiomB] : L.HasAxiomN := ⟨nec verum⟩

/-! #### The axiom `P` -/

instance [L.HasAxiomM] [L.HasAxiomD] : L.HasAxiomP := by
  constructor;
  have h₁ : (⊥ : Formula α) 🡒 ∼⊥ ∈ L := efq;
  have h₂ : □(⊥ : Formula α) 🡒 □(∼⊥) ∈ L := rm h₁;
  have h₃ : □(⊥ : Formula α) 🡒 ◇(⊥ : Formula α) ∈ L := axiomD;
  exact mdp₁ h₃ h₂;

omit [L.HasRE] in
instance [L.HasAxiomN] [L.HasAxiomD] : L.HasAxiomP := by
  constructor;
  have h₁ : □(⊥ : Formula α) 🡒 ◇(⊥ : Formula α) ∈ L := axiomD;
  have h₂ : ∼∼□⊤ 🡒 ∼□⊥ ∈ L := contra h₁;
  have h₃ : ∼∼□⊤ ∈ L := dni' axiomN;
  exact h₂ ⨀ h₃;

omit [L.HasRE] in
instance [L.HasAxiomT] : L.HasAxiomP := by
  constructor;
  have h₁ : (⊤ : Formula α) 🡒 ∼□⊥ ∈ L := contra axiomT;
  exact h₁ ⨀ verum;

/-! #### The axiom scheme `D` -/

instance [L.HasAxiomC] [L.HasAxiomP] : L.HasAxiomD := by
  constructor;
  intro A;
  have h₁ : (A ⋏ ∼A) 🡘 ⊥ ∈ L := E_intro CKNO efq;
  have h₂ : □(A ⋏ ∼A) 🡘 □⊥ ∈ L := re h₁;
  have h₃ : □(A ⋏ ∼A) 🡒 □⊥ ∈ L := C_of_E_mp h₂;
  have h₄ : □⊥ 🡒 ⊥ ∈ L := axiomP;
  have h₅ : □(A ⋏ ∼A) 🡒 ⊥ ∈ L := C_trans h₃ h₄;
  have h₆ : (□A ⋏ □(∼A)) 🡒 □(A ⋏ ∼A) ∈ L := axiomC;
  have h₇ : (□A ⋏ □(∼A)) 🡒 ⊥ ∈ L := C_trans h₆ h₅;
  exact CK_iff_CC.mp h₇;

omit [L.HasRE] in
instance [L.HasAxiomK] [L.HasAxiomP] : L.HasAxiomD := by
  constructor;
  intro A;
  have h₁ : □(∼A) 🡒 (□A 🡒 □⊥) ∈ L := axiomK;
  have h₂ : (□A 🡒 □⊥) 🡒 (□A 🡒 ⊥) ∈ L := CCC_of_C_right axiomP;
  have h₃ : □(∼A) 🡒 (□A 🡒 ⊥) ∈ L := C_trans h₁ h₂;
  have h₄ : ∼∼□A 🡒 ◇A ∈ L := contra h₃;
  exact C_trans dni h₄;

omit [L.HasRE] in
instance [L.HasAxiomT] : L.HasAxiomD := by
  constructor;
  intro A;
  have h₁ : □A 🡒 A ∈ L := axiomT;
  have h₂ : A 🡒 ◇A ∈ L := diaTc;
  exact C_trans h₁ h₂;

/-! #### The axiom scheme `T` -/

instance [L.HasAxiomD] [L.HasAxiomB] [L.HasAxiomFour] : L.HasAxiomT := by
  constructor;
  intro A;
  have h₁ : □A 🡒 □□A ∈ L := axiomFour;
  have h₂ : □□A 🡒 ◇□A ∈ L := axiomD;
  have h₃ : □A 🡒 ◇□A ∈ L := C_trans h₁ h₂;
  have h₄ : ◇□A 🡒 A ∈ L := diaBc;
  exact C_trans h₃ h₄;

instance [L.HasAxiomC] [L.HasAxiomD] [L.HasAxiomB] [L.HasAxiomFive] : L.HasAxiomT := by
  constructor;
  intro A;
  have h₁ : ◇□A ⋏ ∼□A 🡒 □A ∈ L := C_trans and₁ diaFivec;
  have h₂ : ◇□A ⋏ ∼□A 🡒 (□A ⋏ ∼□A) ∈ L := CK_of_C_of_C h₁ and₂;
  have h₃ : ◇□A ⋏ ∼□A 🡒 ⊥ ∈ L := C_trans h₂ CKNO;
  have h₄ : ◇□A ⋏ ∼□A 🡘 ⊥ ∈ L := E_intro h₃ efq;
  have h₅ : □(◇□A ⋏ ∼□A) 🡘 □⊥ ∈ L := re h₄;
  have h₆ : □A 🡒 □◇□A ∈ L := axiomB;
  have h₇ : ∼A 🡒 □(∼□A) ∈ L := CNBoxNBox;
  have h₈ : □A ⋏ ∼A 🡒 (□◇□A ⋏ □(∼□A)) ∈ L := CK_of_C_of_C (C_trans and₁ h₆) (C_trans and₂ h₇);
  have h₉ : (□◇□A ⋏ □(∼□A)) 🡒 □(◇□A ⋏ ∼□A) ∈ L := axiomC;
  have h₁₀ : □A ⋏ ∼A 🡒 □(◇□A ⋏ ∼□A) ∈ L := C_trans h₈ h₉;
  have h₁₁ : □(◇□A ⋏ ∼□A) 🡒 □⊥ ∈ L := C_of_E_mp h₅;
  have h₁₂ : □A ⋏ ∼A 🡒 □⊥ ∈ L := C_trans h₁₀ h₁₁;
  have h₁₃ : □A ⋏ ∼A 🡒 ⊥ ∈ L := C_trans h₁₂ axiomP;
  have h₁₄ : □A 🡒 ∼∼A ∈ L := CK_iff_CC.mp h₁₃;
  exact C_trans h₁₄ dne;

/-! #### The axiom scheme `B` -/

omit [L.HasRE] in
instance [L.HasAxiomT] [L.HasAxiomFive] : L.HasAxiomB := by
  constructor;
  intro A;
  have h₁ : A 🡒 ◇A ∈ L := diaTc;
  have h₂ : ◇A 🡒 □◇A ∈ L := axiomFive;
  exact C_trans h₁ h₂;

/-! #### The axiom scheme `Four` -/

instance [L.HasAxiomM] [L.HasAxiomB] [L.HasAxiomFive] : L.HasAxiomFour := by
  constructor;
  intro A;
  have h₁ : ◇□A 🡒 □A ∈ L := diaFivec;
  have h₂ : □◇□A 🡒 □□A ∈ L := rm h₁;
  have h₃ : □A 🡒 □◇□A ∈ L := axiomB;
  exact C_trans h₃ h₂;

instance [L.HasAxiomT] [L.HasAxiomFive] : L.HasAxiomFour := by
  constructor;
  intro A;
  have h₁ : □A 🡘 ◇□A ∈ L := E_intro diaTc diaFivec;
  have h₂ : □□A 🡘 □◇□A ∈ L := re h₁;
  have h₃ : □◇□A 🡒 □□A ∈ L := C_of_E_mpr h₂;
  have h₄ : □A 🡒 □◇□A ∈ L := axiomB;
  exact C_trans h₄ h₃;

/-! #### The axiom scheme `Five` -/

instance [L.HasAxiomM] [L.HasAxiomB] [L.HasAxiomFour] : L.HasAxiomFive := by
  constructor;
  intro A;
  have h₁ : ◇◇A 🡒 ◇A ∈ L := diaFourc;
  have h₂ : □◇◇A 🡒 □◇A ∈ L := rm h₁;
  have h₃ : ◇A 🡒 □◇◇A ∈ L := axiomB;
  exact C_trans h₃ h₂;

instance [L.HasAxiomD] [L.HasAxiomB] [L.HasAxiomFour] : L.HasAxiomFive := by
  constructor;
  intro A;
  have h₁ : ◇A 🡒 □◇◇A ∈ L := axiomB;
  have h₂ : □◇◇A 🡒 ◇◇◇A ∈ L := axiomD;
  have h₃ : ◇◇◇A 🡒 ◇◇A ∈ L := diaFourc;
  have h₄ : □◇◇A 🡒 ◇◇A ∈ L := C_trans h₂ h₃;
  have h₅ : ◇A 🡒 ◇◇A ∈ L := C_trans h₁ h₄;
  have h₆ : ◇◇A 🡘 ◇A ∈ L := E_intro diaFourc h₅;
  have h₇ : □◇◇A 🡘 □◇A ∈ L := re h₆;
  have h₈ : □◇◇A 🡒 □◇A ∈ L := C_of_E_mp h₇;
  exact C_trans h₁ h₈;

instance [L.HasAxiomT] [L.HasAxiomB] [L.HasAxiomFour] : L.HasAxiomFive := by
  constructor;
  intro A;
  have h₁ : ◇A 🡘 ◇◇A ∈ L := E_intro diaTc diaFourc;
  have h₂ : □◇A 🡘 □◇◇A ∈ L := re h₁;
  have h₃ : □◇◇A 🡒 □◇A ∈ L := C_of_E_mpr h₂;
  have h₄ : ◇A 🡒 □◇◇A ∈ L := axiomB;
  exact C_trans h₄ h₃;

end

end

end Logic

end
