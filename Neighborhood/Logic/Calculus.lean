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

lemma re [L.HasRE] : A 🡘 B ∈ L → □A 🡘 □B ∈ L := HasRE.re

lemma multire [L.HasRE] (h : A 🡘 B ∈ L) : □^[n]A 🡘 □^[n]B ∈ L := by
  induction n with
  | zero => simpa;
  | succ n ih => simpa using re ih;

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

@[simp] lemma axiomK [L.HasAxiomK] : □(A 🡒 B) 🡒 □A 🡒 □B ∈ L := HasAxiomK.K ..
@[simp] lemma axiomM [L.HasAxiomM] : □(A ⋏ B) 🡒 (□A ⋏ □B) ∈ L := HasAxiomM.M ..
@[simp] lemma axiomC [L.HasAxiomC] : (□A ⋏ □B) 🡒 □(A ⋏ B) ∈ L := HasAxiomC.C ..
@[simp] lemma axiomN [L.HasAxiomN] : □(⊤ : Formula α) ∈ L := HasAxiomN.N
@[simp] lemma axiomT [L.HasAxiomT] : □A 🡒 A ∈ L := HasAxiomT.T ..
@[simp] lemma axiomB [L.HasAxiomB] : A 🡒 □◇A ∈ L := HasAxiomB.B ..
@[simp] lemma axiomD [L.HasAxiomD] : □A 🡒 ◇A ∈ L := HasAxiomD.D ..
@[simp] lemma axiomP [L.HasAxiomP] : ∼□(⊥ : Formula α) ∈ L := HasAxiomP.P
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

@[simp] lemma axiomK' [L.HasAxiomK] (h : □(A 🡒 B) ∈ L) : □A 🡒 □B ∈ L := axiomK ⨀ h
@[simp] lemma axiomK'' [L.HasAxiomK] (h₁ : □(A 🡒 B) ∈ L) (h₂ : □A ∈ L) : □B ∈ L := axiomK' h₁ ⨀ h₂
lemma axiomM' [L.HasAxiomM] (h : □(A ⋏ B) ∈ L) : □A ⋏ □B ∈ L := axiomM ⨀ h
lemma axiomC' [L.HasAxiomC] (h : □A ⋏ □B ∈ L) : □(A ⋏ B) ∈ L := axiomC ⨀ h
@[simp] lemma axiomT' [L.HasAxiomT] (h : □A ∈ L) : A ∈ L := axiomT ⨀ h
lemma axiomD' [L.HasAxiomD] (h : □A ∈ L) : ◇A ∈ L := axiomD ⨀ h
@[simp] lemma axiomB' [L.HasAxiomB] (h : A ∈ L) : □◇A ∈ L := axiomB ⨀ h

/-! ### The monotonicity rule -/

/-- The monotonicity rule for `□`, derived from `RE` and the axiom scheme `M`. -/
lemma rm [L.HasRE] [L.HasAxiomM] (h : A 🡒 B ∈ L) : □A 🡒 □B ∈ L := by
  have h₁ : □A 🡒 □(A ⋏ B) ∈ L :=
    C_of_E_mp <| re <| E_intro (CK_of_C_of_C C_id h) and₁;
  exact C_trans (C_trans h₁ axiomM) and₂;

/-- The monotonicity rule for `◇`, derived from `RE` and the axiom scheme `M`. -/
lemma rmDia [L.HasRE] [L.HasAxiomM] (h : A 🡒 B ∈ L) : ◇A 🡒 ◇B ∈ L :=
  contra <| rm <| contra h

/-! ### Derived axiom schemes -/

section

variable [L.HasRE]

/-- If `A 🡒 B` is a theorem, then `□A 🡒 □B` is a theorem, derived from `K` and `N`. -/
private lemma box_mono_of_KN [L.HasAxiomK] [L.HasAxiomN] (h : A 🡒 B ∈ L) : □A 🡒 □B ∈ L :=
  axiomK' (C_of_E_mpr (re (E_intro (C_of_conseq verum) (C_of_conseq h))) ⨀ axiomN)

/-- The axiom scheme `M` is derivable from `K` and `N`. -/
instance [L.HasAxiomK] [L.HasAxiomN] : L.HasAxiomM :=
  ⟨fun _ _ => CK_of_C_of_C (box_mono_of_KN and₁) (box_mono_of_KN and₂)⟩

/-- The axiom scheme `C` is derivable from `M` and `K`. -/
instance [L.HasAxiomM] [L.HasAxiomK] : L.HasAxiomC := ⟨by
  intro A B;
  have h₁ : □A 🡒 □(B 🡒 A) ∈ L := rm implyK;
  have h₂ : □(B 🡒 A) 🡒 □(B 🡒 A ⋏ B) ∈ L :=
    C_of_E_mp <| re <| E_intro
      (CK_iff_CC.mp <| CK_of_C_of_C (mdp₁ and₁ and₂) and₂)
      (CCC_of_C_right and₁);
  exact mdp₁ (C_trans (C_trans and₁ (C_trans h₁ h₂)) axiomK) and₂;⟩

/-- The axiom scheme `K` is derivable from `M` and `C`. -/
lemma axiomK_of_MC [L.HasAxiomM] [L.HasAxiomC] : □(A 🡒 B) 🡒 □A 🡒 □B ∈ L :=
  CK_iff_CC.mp <| C_trans axiomC <| rm <| mdp₁ and₁ and₂

instance [L.HasAxiomM] [L.HasAxiomC] : L.HasAxiomK := ⟨fun _ _ => axiomK_of_MC⟩

/-- The dual of the axiom scheme `B`. -/
lemma diaBc [L.HasAxiomB] : ◇□A 🡒 A ∈ L := by
  have h₁ : ∼∼A 🡘 A ∈ L := E_intro dne dni;
  have h₂ : ◇(∼A) 🡘 ∼□A ∈ L :=
    E_intro (contra (C_of_E_mpr (re h₁))) (contra (C_of_E_mp (re h₁)));
  have h₃ : ∼A 🡒 □(∼□A) ∈ L := C_trans axiomB (C_of_E_mp (re h₂));
  exact C_trans (contra h₃) dne;

/-- The axiom scheme `C` is derivable from `M` and `B`. -/
instance [L.HasAxiomM] [L.HasAxiomB] : L.HasAxiomC := ⟨by
  intro A B;
  have h₁ : (□A ⋏ □B) 🡒 □◇(□A ⋏ □B) ∈ L := axiomB;
  have h₂ : ◇(□A ⋏ □B) 🡒 A ∈ L := C_trans (rmDia and₁) diaBc;
  have h₃ : ◇(□A ⋏ □B) 🡒 B ∈ L := C_trans (rmDia and₂) diaBc;
  have h₅ : □◇(□A ⋏ □B) 🡒 □(A ⋏ B) ∈ L := rm (CK_of_C_of_C h₂ h₃);
  exact C_trans h₁ h₅;⟩

/-- The axiom `N` is derivable from `M` and `B`. -/
instance [L.HasAxiomM] [L.HasAxiomB] : L.HasAxiomN :=
  ⟨rm (C_of_conseq verum) ⨀ axiomB' verum⟩

/-- The axiom `N` is derivable from `M` and `5`. -/
instance [L.HasAxiomM] [L.HasAxiomFive] : L.HasAxiomN := ⟨by
  have h_left : □(∼(⊤ : Formula α)) 🡒 □◇⊤ ∈ L := rm (mdp₁ CNC (C_of_conseq verum));
  have h_right : ∼(□(∼(⊤ : Formula α))) 🡒 □◇⊤ ∈ L := axiomFive;
  have h_dia : □◇(⊤ : Formula α) ∈ L := of_C_of_C_of_A h_left h_right lem;
  exact rm (C_of_conseq verum) ⨀ h_dia;⟩

/-- The axiom `N` is derivable from `B` and `4`. -/
instance [L.HasAxiomB] [L.HasAxiomFour] : L.HasAxiomN := ⟨by
  have h₁ : □◇(⊤ : Formula α) ∈ L := axiomB' verum;
  have h₂ : □□◇(⊤ : Formula α) ∈ L := axiomFour ⨀ h₁;
  have h₃ : □◇(⊤ : Formula α) 🡘 ⊤ ∈ L := E_intro (C_of_conseq verum) (C_of_conseq h₁);
  have h₄ : □□◇(⊤ : Formula α) 🡘 □⊤ ∈ L := re h₃;
  exact C_of_E_mp h₄ ⨀ h₂;⟩

/-- `◇⊤` is derivable from the axiom `P`. -/
private lemma diaTop_of_P [L.HasAxiomP] : ◇(⊤ : Formula α) ∈ L :=
  C_trans (C_of_E_mp (re (E_intro dne efq))) axiomP

/-- The axiom `N` is derivable from `P` and `5`. -/
instance [L.HasAxiomP] [L.HasAxiomFive] : L.HasAxiomN := ⟨by
  have h₁ : ◇(⊤ : Formula α) ∈ L := diaTop_of_P;
  have h₂ : □◇(⊤ : Formula α) ∈ L := axiomFive ⨀ h₁;
  have h₃ : ◇(⊤ : Formula α) 🡘 ⊤ ∈ L := E_intro (C_of_conseq verum) (C_of_conseq h₁);
  have h₄ : □◇(⊤ : Formula α) 🡘 □⊤ ∈ L := re h₃;
  exact C_of_E_mp h₄ ⨀ h₂;⟩

/-- The axiom `N` is derivable from `P` and `B`. -/
instance [L.HasAxiomP] [L.HasAxiomB] : L.HasAxiomN := ⟨by
  have h₁ : ◇(⊤ : Formula α) ∈ L := diaTop_of_P;
  have h₂ : □◇(⊤ : Formula α) ∈ L := axiomB' verum;
  have h₃ : ◇(⊤ : Formula α) 🡘 ⊤ ∈ L := E_intro (C_of_conseq verum) (C_of_conseq h₁);
  have h₄ : □◇(⊤ : Formula α) 🡘 □⊤ ∈ L := re h₃;
  exact C_of_E_mp h₄ ⨀ h₂;⟩

/-- The axiom `N` is derivable from `D`, `B` and `5`. -/
instance [L.HasAxiomD] [L.HasAxiomB] [L.HasAxiomFive] : L.HasAxiomN := ⟨by
  have h₁ : □◇(⊤ : Formula α) ∈ L := axiomB' verum;
  have h₂ : ◇◇(⊤ : Formula α) ∈ L := axiomD ⨀ h₁;
  have h₃ : □◇◇(⊤ : Formula α) ∈ L := axiomFive ⨀ h₂;
  have h₄ : ◇◇(⊤ : Formula α) 🡘 ⊤ ∈ L := E_intro (C_of_conseq verum) (C_of_conseq h₂);
  have h₅ : □◇◇(⊤ : Formula α) 🡘 □⊤ ∈ L := re h₄;
  exact C_of_E_mp h₅ ⨀ h₃;⟩

/-- The dual of the axiom scheme `Four`. -/
lemma diaFourc [L.HasAxiomFour] : ◇◇A 🡒 ◇A ∈ L := by
  have e : ∼◇A 🡘 □(∼A) ∈ L := E_intro dne dni;
  have h : □(∼A) 🡒 □(∼◇A) ∈ L := C_trans axiomFour (C_of_E_mp (re (E_symm e)));
  exact contra h;

/-- The axiom scheme `Five` is derivable from `M`, `B` and `4`. -/
instance [L.HasAxiomM] [L.HasAxiomB] [L.HasAxiomFour] : L.HasAxiomFive :=
  ⟨fun _ => C_trans axiomB (rm diaFourc)⟩

/-- The axiom scheme `Five` is derivable from `D`, `B` and `4`. -/
instance [L.HasAxiomD] [L.HasAxiomB] [L.HasAxiomFour] : L.HasAxiomFive := ⟨fun A => by
  have h₁ : ◇A 🡒 ◇◇A ∈ L := C_trans axiomB (C_trans axiomD diaFourc);
  have e : ◇◇A 🡘 ◇A ∈ L := E_intro diaFourc h₁;
  exact C_trans axiomB (C_of_E_mp (re e))⟩

/-- The axiom scheme `T` is derivable from `D`, `B` and `4`. -/
instance [L.HasAxiomD] [L.HasAxiomB] [L.HasAxiomFour] : L.HasAxiomT := ⟨fun A => by
  have hdia : ∀ {A : Formula α}, A 🡒 ◇A ∈ L :=
    fun {A} => C_trans axiomB (C_trans (axiomD (A := ◇A)) diaFourc);
  have h₁ : ∼∼A 🡘 A ∈ L := E_intro dne dni;
  have h₂ : ◇(∼A) 🡒 ∼□A ∈ L := contra (C_of_E_mpr (re h₁));
  have h₃ : ∼A 🡒 ∼□A ∈ L := C_trans hdia h₂;
  exact C_trans dni (C_trans (contra h₃) dne);⟩

/-- The dual of the axiom scheme `Five`. -/
lemma diaFivec [L.HasAxiomFive] : ◇□A 🡒 □A ∈ L := by
  have h₁ : ∼∼A 🡘 A ∈ L := E_intro dne dni;
  have h₂ : ◇(∼A) 🡘 ∼□A ∈ L :=
    E_intro (contra (C_of_E_mpr (re h₁))) (contra (C_of_E_mp (re h₁)));
  have h₃ : ∼□A 🡒 □(∼□A) ∈ L := C_trans (C_of_E_mpr h₂) (C_trans axiomFive (C_of_E_mp (re h₂)));
  exact C_trans (contra h₃) dne;

/-- The axiom scheme `Four` is derivable from `M`, `B` and `5`. -/
instance [L.HasAxiomM] [L.HasAxiomB] [L.HasAxiomFive] : L.HasAxiomFour :=
  ⟨fun _ => C_trans axiomB (rm diaFivec)⟩

/-- The axiom scheme `D` is derivable from `C` and `P`. -/
instance [L.HasAxiomC] [L.HasAxiomP] : L.HasAxiomD := ⟨fun A => by
  have h₁ : (A ⋏ ∼A) 🡘 (⊥ : Formula α) ∈ L := E_intro CKNO efq;
  have h₂ : □A ⋏ □(∼A) 🡒 (⊥ : Formula α) ∈ L :=
    C_trans axiomC (C_trans (C_of_E_mp (re h₁)) axiomP);
  exact CK_iff_CC.mp h₂;⟩

omit [L.HasRE] in
/-- The axiom scheme `D` is derivable from `K` and `P`. -/
instance [L.HasAxiomK] [L.HasAxiomP] : L.HasAxiomD :=
  ⟨fun _ => C_trans dni (contra (C_trans (axiomK (B := ⊥)) (CCC_of_C_right axiomP)))⟩

omit [L.HasRE] in
/-- The axiom `P` is derivable from `N` and `D`. -/
lemma axiomP_of_ND [L.HasAxiomN] [L.HasAxiomD] : Axioms.P ∈ (L : Logic α) :=
  contra (axiomD (A := ⊥)) ⨀ dni' axiomN

omit [L.HasRE] in
instance [L.HasAxiomN] [L.HasAxiomD] : L.HasAxiomP := ⟨axiomP_of_ND⟩

/-- The axiom `P` is derivable from `M` and `D`. -/
lemma axiomP_of_MD [L.HasAxiomM] [L.HasAxiomD] : Axioms.P ∈ (L : Logic α) :=
  mdp₁ (axiomD (A := ⊥)) (rm efq)

instance [L.HasAxiomM] [L.HasAxiomD] : L.HasAxiomP := ⟨axiomP_of_MD⟩

/-- The axiom scheme `T` is derivable from `D`, `B` and `4`. -/
instance [L.HasAxiomD] [L.HasAxiomB] [L.HasAxiomFour] : L.HasAxiomT :=
  ⟨fun _ => C_trans axiomFour (C_trans axiomD diaBc)⟩

variable [L.HasAxiomT]

omit [L.HasRE] in
/-- The dual of the axiom scheme `T`. -/
lemma diaTc : A 🡒 ◇A ∈ L := C_trans dni (contra axiomT)

omit [L.HasRE] in
/-- The axiom scheme `D` is derivable from `T`. -/
instance : L.HasAxiomD := ⟨fun _ => C_trans axiomT diaTc⟩

omit [L.HasRE] in
/-- The axiom `P` is derivable from `T`. -/
instance : L.HasAxiomP := ⟨contra (axiomT (A := ⊥)) ⨀ verum⟩

/-- The axiom scheme `B` is derivable from `T` and `5`. -/
instance [L.HasAxiomFive] : L.HasAxiomB := ⟨fun _ => C_trans diaTc axiomFive⟩

/-- The axiom scheme `Four` is derivable from `T` and `5`. -/
instance [L.HasAxiomFive] : L.HasAxiomFour := ⟨fun A => by
  have e : □A 🡘 ◇□A ∈ L := E_intro diaTc diaFivec;
  exact C_trans axiomB (C_of_E_mpr (re e))⟩

/-- The axiom scheme `Five` is derivable from `T`, `B` and `4`. -/
instance [L.HasAxiomB] [L.HasAxiomFour] : L.HasAxiomFive := ⟨fun A => by
  have e : ◇A 🡘 ◇◇A ∈ L := E_intro diaTc diaFourc;
  exact C_trans axiomB (C_of_E_mpr (re e))⟩

/-- The necessitation rule, derived from `RE` and the axiom schemes `T` and `B`. -/
lemma nec [L.HasAxiomB] (h : A ∈ L) : □A ∈ L :=
  C_of_E_mpr (re <| E_intro diaTc (C_of_conseq h)) ⨀ (axiomB ⨀ h)

/-- The axiom `N` is derivable from `T` and `B`. -/
instance [L.HasAxiomB] : L.HasAxiomN := ⟨nec verum⟩

end

end

end Logic

end
