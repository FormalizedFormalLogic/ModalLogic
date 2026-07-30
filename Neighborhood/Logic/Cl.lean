module

public import Neighborhood.Axioms
public import Neighborhood.Logic.Basic

/-!
# Classical propositional reasoning inside a logic

Closure of a logic under classical propositional reasoning, presented by modus ponens together
with the axiom schemes `ImplyK`, `ImplyS`, `DNE`, `AndElim₁`, `AndElim₂`, `AndIntro`,
`OrIntro₁`, `OrIntro₂` and `OrElim`, and the toolkit of propositional inferences derived from it.
Since negation, conjunction, disjunction and biimplication are abbreviations for implications
and `⊥`, the toolkit is stated directly in terms of them.
-/

@[expose] public section

variable {α : Type u}

namespace Logic

variable {L : Logic α} {A A₁ A₂ B B₁ B₂ C D : Formula α}

/-! ### Closure condition -/

/-- A logic closed under classical propositional reasoning. -/
class Cl (L : Logic α) where
  mdp : ∀ {A B : Formula α}, A 🡒 B ∈ L → A ∈ L → B ∈ L
  implyK : ∀ (A B : Formula α), Axioms.ImplyK A B ∈ L
  implyS : ∀ (A B C : Formula α), Axioms.ImplyS A B C ∈ L
  dne : ∀ (A : Formula α), Axioms.DNE A ∈ L
  andElim₁ : ∀ (A B : Formula α), Axioms.AndElim₁ A B ∈ L
  andElim₂ : ∀ (A B : Formula α), Axioms.AndElim₂ A B ∈ L
  andIntro : ∀ (A B : Formula α), Axioms.AndIntro A B ∈ L
  orIntro₁ : ∀ (A B : Formula α), Axioms.OrIntro₁ A B ∈ L
  orIntro₂ : ∀ (A B : Formula α), Axioms.OrIntro₂ A B ∈ L
  orElim : ∀ (A B C : Formula α), Axioms.OrElim A B C ∈ L

section

variable [L.Cl]

lemma mdp! : A 🡒 B ∈ L → A ∈ L → B ∈ L := Cl.mdp

@[inherit_doc] infixl:90 "⨀" => mdp!

@[simp] lemma implyK! : A 🡒 B 🡒 A ∈ L := Cl.implyK ..
@[simp] lemma implyS! : (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 A 🡒 C ∈ L := Cl.implyS ..
@[simp] lemma dne! : ∼∼A 🡒 A ∈ L := Cl.dne ..
@[simp] lemma and₁! : A ⋏ B 🡒 A ∈ L := Cl.andElim₁ ..
@[simp] lemma and₂! : A ⋏ B 🡒 B ∈ L := Cl.andElim₂ ..
@[simp] lemma and₃! : A 🡒 B 🡒 A ⋏ B ∈ L := Cl.andIntro ..
@[simp] lemma or₁! : A 🡒 A ⋎ B ∈ L := Cl.orIntro₁ ..
@[simp] lemma or₂! : B 🡒 A ⋎ B ∈ L := Cl.orIntro₂ ..
@[simp] lemma or₃! : (A 🡒 C) 🡒 (B 🡒 C) 🡒 (A ⋎ B) 🡒 C ∈ L := Cl.orElim ..

/-! ### Implication -/

lemma C!_of_conseq! (h : A ∈ L) : B 🡒 A ∈ L := implyK! ⨀ h

alias dhyp! := C!_of_conseq!

@[simp] lemma C!_id : A 🡒 A ∈ L := implyS! (B := A 🡒 A) ⨀ implyK! ⨀ implyK!

@[grind →] lemma mdp₁! (hC : A 🡒 B 🡒 C ∈ L) (hB : A 🡒 B ∈ L) : A 🡒 C ∈ L := implyS! ⨀ hC ⨀ hB

@[inherit_doc] infixl:90 "⨀₁" => mdp₁!

@[grind →]
lemma mdp₂! (hD : A 🡒 B 🡒 C 🡒 D ∈ L) (hC : A 🡒 B 🡒 C ∈ L) : A 🡒 B 🡒 D ∈ L :=
  C!_of_conseq! implyS! ⨀₁ hD ⨀₁ hC

@[inherit_doc] infixl:90 "⨀₂" => mdp₂!

@[grind →]
lemma mdp₃! {F : Formula α} (hF : A 🡒 B 🡒 C 🡒 D 🡒 F ∈ L) (hD : A 🡒 B 🡒 C 🡒 D ∈ L) :
    A 🡒 B 🡒 C 🡒 F ∈ L :=
  C!_of_conseq! (C!_of_conseq! implyS!) ⨀₂ hF ⨀₂ hD

@[inherit_doc] infixl:90 "⨀₃" => mdp₃!

@[grind →]
lemma mdp₄! {F G : Formula α} (hG : A 🡒 B 🡒 C 🡒 D 🡒 F 🡒 G ∈ L) (hF : A 🡒 B 🡒 C 🡒 D 🡒 F ∈ L) :
    A 🡒 B 🡒 C 🡒 D 🡒 G ∈ L :=
  C!_of_conseq! (C!_of_conseq! (C!_of_conseq! implyS!)) ⨀₃ hG ⨀₃ hF

@[inherit_doc] infixl:90 "⨀₄" => mdp₄!

@[grind <=]
lemma C!_trans (hB : A 🡒 B ∈ L) (hC : B 🡒 C ∈ L) : A 🡒 C ∈ L := mdp₁! (C!_of_conseq! hC) hB

lemma C!_swap (h : A 🡒 B 🡒 C ∈ L) : B 🡒 A 🡒 C ∈ L := C!_trans implyK! (implyS! ⨀ h)

@[grind .] lemma CCCC! : A 🡒 B 🡒 C 🡒 A ∈ L := C!_trans implyK! implyK!

@[simp] lemma CCC! : (A 🡒 B) 🡒 (B 🡒 C) 🡒 (A 🡒 C) ∈ L := C!_swap (C!_trans implyK! implyS!)

lemma CCC!_of_C!_right (h : B 🡒 C ∈ L) : (A 🡒 B) 🡒 (A 🡒 C) ∈ L := implyS! ⨀ C!_of_conseq! h

lemma CCC!_of_C!_left (h : B 🡒 A ∈ L) : (A 🡒 C) 🡒 (B 🡒 C) ∈ L := CCC! ⨀ h

@[simp] lemma CCCCC! : (A 🡒 B 🡒 C) 🡒 (B 🡒 A 🡒 C) ∈ L := C!_trans implyS! (CCC!_of_C!_left implyK!)

@[simp] lemma verum! : (⊤ : Formula α) ∈ L := C!_id

@[simp] lemma CV! : A 🡒 ⊤ ∈ L := C!_of_conseq! verum!

/-! ### Negation -/

omit [L.Cl] in
@[grind =] lemma N!_iff_CO! : ∼A ∈ L ↔ A 🡒 ⊥ ∈ L := Iff.rfl

@[simp] lemma efq! : ⊥ 🡒 A ∈ L := C!_trans implyK! dne!

@[grind ⇒] lemma of_O! (h : (⊥ : Formula α) ∈ L) : A ∈ L := efq! ⨀ h

@[simp] lemma NO! : ∼(⊥ : Formula α) ∈ L := C!_id

@[grind ⇒] lemma of_NN! (h : ∼∼A ∈ L) : A ∈ L := dne! ⨀ h

@[simp] lemma dni! : A 🡒 ∼∼A ∈ L := C!_swap C!_id

lemma dni'! (h : A ∈ L) : ∼∼A ∈ L := dni! ⨀ h

@[simp] lemma CCNN! : (A 🡒 B) 🡒 (∼B 🡒 ∼A) ∈ L := CCC!

@[simp]
lemma elimContra! : (∼B 🡒 ∼A) 🡒 (A 🡒 B) ∈ L :=
  CCC!_of_C!_right (CCC!_of_C!_right dne!) ⨀ (CCC!_of_C!_right CCCCC! ⨀ C!_id)

lemma contra! (h : A 🡒 B ∈ L) : ∼B 🡒 ∼A ∈ L := CCNN! ⨀ h

lemma neg_mdp (hA : ∼A ∈ L) (h : A ∈ L) : (⊥ : Formula α) ∈ L := hA ⨀ h

lemma explode! (h₁ : A ∈ L) (h₂ : ∼A ∈ L) : B ∈ L := of_O! <| neg_mdp h₂ h₁

@[simp] lemma CNC! : ∼A 🡒 A 🡒 B ∈ L := C!_swap CCC! ⨀ efq!

lemma C_of_N (h : ∼A ∈ L) : A 🡒 B ∈ L := CNC! ⨀ h

lemma CN!_of_CN!_left (h : ∼A 🡒 B ∈ L) : ∼B 🡒 A ∈ L := C!_trans (contra! h) dne!

lemma CN!_of_CN!_right (h : A 🡒 ∼B ∈ L) : B 🡒 ∼A ∈ L := C!_trans dni! (contra! h)

lemma C!_of_CNN! (h : ∼A 🡒 ∼B ∈ L) : B 🡒 A ∈ L := elimContra! ⨀ h

/-! ### Conjunction -/

@[grind ->] lemma K!_left (h : A ⋏ B ∈ L) : A ∈ L := and₁! ⨀ h

@[grind ->] lemma K!_right (h : A ⋏ B ∈ L) : B ∈ L := and₂! ⨀ h

@[grind <-] lemma K!_intro (h₁ : A ∈ L) (h₂ : B ∈ L) : A ⋏ B ∈ L := and₃! ⨀ h₁ ⨀ h₂

@[grind =] lemma K!_intro_iff : A ⋏ B ∈ L ↔ A ∈ L ∧ B ∈ L :=
  ⟨fun h => ⟨K!_left h, K!_right h⟩, fun ⟨h₁, h₂⟩ => K!_intro h₁ h₂⟩

@[grind <=] lemma CK!_of_C!_of_C! (hB : A 🡒 B ∈ L) (hC : A 🡒 C ∈ L) : A 🡒 B ⋏ C ∈ L :=
  mdp₁! (C!_trans hB and₃!) hC

alias right_K!_intro := CK!_of_C!_of_C!

@[simp, grind .] lemma CKK! : A ⋏ B 🡒 B ⋏ A ∈ L := CK!_of_C!_of_C! and₂! and₁!

@[grind <-] lemma K!_symm (h : A ⋏ B ∈ L) : B ⋏ A ∈ L := CKK! ⨀ h

@[simp, grind .]
lemma ECKCC! : (A ⋏ B 🡒 C) 🡘 (A 🡒 B 🡒 C) ∈ L :=
  K!_intro
    (C!_of_conseq! CCC! ⨀₁ C!_of_conseq! and₃! ⨀₁ (CCCCC! ⨀ CCC!))
    (C!_trans (CCC! ⨀ and₁!) (C!_swap implyS! ⨀ and₂!))

@[grind =] lemma CK!_iff_CC! : A ⋏ B 🡒 C ∈ L ↔ A 🡒 B 🡒 C ∈ L :=
  ⟨fun h => C!_trans and₃! (CCC!_of_C!_right h),
   fun h => mdp₁! (C!_trans and₁! h) and₂!⟩

@[simp] lemma CKNO! : A ⋏ ∼A 🡒 ⊥ ∈ L := CK!_iff_CC!.mpr dni!

lemma O!_intro_of_KN! (h : A ⋏ ∼A ∈ L) : (⊥ : Formula α) ∈ L := CKNO! ⨀ h

/-! ### Disjunction -/

@[grind .] lemma A!_intro_left (h : A ∈ L) : A ⋎ B ∈ L := or₁! ⨀ h

@[grind .] lemma A!_intro_right (h : B ∈ L) : A ⋎ B ∈ L := or₂! ⨀ h

lemma left_A!_intro (h₁ : A 🡒 C ∈ L) (h₂ : B 🡒 C ∈ L) : A ⋎ B 🡒 C ∈ L := or₃! ⨀ h₁ ⨀ h₂

lemma of_C!_of_C!_of_A! (h₁ : A 🡒 C ∈ L) (h₂ : B 🡒 C ∈ L) (h₃ : A ⋎ B ∈ L) : C ∈ L :=
  left_A!_intro h₁ h₂ ⨀ h₃

@[simp] lemma lem! : A ⋎ ∼A ∈ L := C!_id

/-! ### Biimplication -/

@[grind ←] lemma E!_intro (h₁ : A 🡒 B ∈ L) (h₂ : B 🡒 A ∈ L) : A 🡘 B ∈ L := K!_intro h₁ h₂

@[simp] lemma E!_id : A 🡘 A ∈ L := E!_intro C!_id C!_id

@[grind →] lemma C_of_E_mp! (h : A 🡘 B ∈ L) : A 🡒 B ∈ L := K!_left h

@[grind →] lemma C_of_E_mpr! (h : A 🡘 B ∈ L) : B 🡒 A ∈ L := K!_right h

@[simp] lemma CEE! : (A 🡘 B) 🡒 (B 🡘 A) ∈ L := CKK!

@[grind <-] lemma E!_symm (h : A 🡘 B ∈ L) : B 🡘 A ∈ L := K!_symm h

@[grind <=] lemma E!_trans (h₁ : A 🡘 B ∈ L) (h₂ : B 🡘 C ∈ L) : A 🡘 C ∈ L :=
  E!_intro (C!_trans (C_of_E_mp! h₁) (C_of_E_mp! h₂)) (C!_trans (C_of_E_mpr! h₂) (C_of_E_mpr! h₁))

@[grind →] lemma iff_of_E! (h : A 🡘 B ∈ L) : A ∈ L ↔ B ∈ L :=
  ⟨fun hA => C_of_E_mp! h ⨀ hA, fun hB => C_of_E_mpr! h ⨀ hB⟩

lemma EKK!_of_E!_of_E! (h₁ : A₁ 🡘 A₂ ∈ L) (h₂ : B₁ 🡘 B₂ ∈ L) : A₁ ⋏ B₁ 🡘 A₂ ⋏ B₂ ∈ L :=
  E!_intro
    (CK!_of_C!_of_C! (C!_trans and₁! (C_of_E_mp! h₁)) (C!_trans and₂! (C_of_E_mp! h₂)))
    (CK!_of_C!_of_C! (C!_trans and₁! (C_of_E_mpr! h₁)) (C!_trans and₂! (C_of_E_mpr! h₂)))

end

end Logic

/-! ### Finite conjunction -/

/-- The conjunction of a finite set of formulas. -/
noncomputable def FormulaFinset.conj (s : FormulaFinset α) : Formula α := s.toList.foldr (· ⋏ ·) ⊤

namespace Logic

variable {L : Logic α} [L.Cl] {A B : Formula α} {Γ Δ : FormulaFinset α}

private lemma left_lconj!_intro {l : List (Formula α)} (h : A ∈ l) : l.foldr (· ⋏ ·) ⊤ 🡒 A ∈ L := by
  induction l with
  | nil => simp at h;
  | cons B l ih =>
    rcases List.mem_cons.mp h with rfl | h;
    . exact and₁!;
    . exact C!_trans and₂! (ih h);

private lemma right_lconj!_intro {l : List (Formula α)} (b : ∀ B ∈ l, A 🡒 B ∈ L) :
    A 🡒 l.foldr (· ⋏ ·) ⊤ ∈ L := by
  induction l with
  | nil => exact CV!;
  | cons B l ih => exact CK!_of_C!_of_C! (b B (by simp)) (ih fun C hC => b C (by simp [hC]));

@[simp] lemma left_Fconj!_intro (h : A ∈ Γ) : Γ.conj 🡒 A ∈ L :=
  left_lconj!_intro (Finset.mem_toList.mpr h)

lemma right_Fconj!_intro (b : ∀ B ∈ Γ, A 🡒 B ∈ L) : A 🡒 Γ.conj ∈ L :=
  right_lconj!_intro fun B hB => b B (Finset.mem_toList.mp hB)

lemma Fconj!_intro (b : ∀ B ∈ Γ, B ∈ L) : Γ.conj ∈ L :=
  right_Fconj!_intro (fun B hB => C!_of_conseq! (b B hB)) ⨀ verum!

@[grind =] lemma Fconj!_iff_forall_provable : Γ.conj ∈ L ↔ ∀ A ∈ Γ, A ∈ L :=
  ⟨fun h _ hA => left_Fconj!_intro hA ⨀ h, Fconj!_intro⟩

lemma CFconj!_Fconj! (h : Δ ⊆ Γ) : Γ.conj 🡒 Δ.conj ∈ L :=
  right_Fconj!_intro fun _ hB => left_Fconj!_intro (h hB)

section
variable [DecidableEq α]

lemma EFconjInsertKFconj! : (insert A Γ).conj 🡘 (A ⋏ Γ.conj) ∈ L := by
  apply E!_intro;
  . exact CK!_of_C!_of_C! (left_Fconj!_intro (by simp)) (CFconj!_Fconj! (by simp));
  . apply right_Fconj!_intro;
    intro B hB;
    rcases Finset.mem_insert.mp hB with rfl | hB;
    . exact and₁!;
    . exact C!_trans and₂! (left_Fconj!_intro hB);

@[simp] lemma CFconjUnionKFconj! : (Γ ∪ Δ).conj 🡒 Γ.conj ⋏ Δ.conj ∈ L :=
  CK!_of_C!_of_C! (CFconj!_Fconj! (by simp)) (CFconj!_Fconj! (by simp))

@[simp] lemma CKFconjFconjUnion! : Γ.conj ⋏ Δ.conj 🡒 (Γ ∪ Δ).conj ∈ L := by
  apply right_Fconj!_intro;
  intro B hB;
  rcases Finset.mem_union.mp hB with hB | hB;
  . exact C!_trans and₁! (left_Fconj!_intro hB);
  . exact C!_trans and₂! (left_Fconj!_intro hB);

end

end Logic

end
