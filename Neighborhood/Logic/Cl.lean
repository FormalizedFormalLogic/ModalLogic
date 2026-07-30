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

namespace LO.Modal

namespace Logic

variable {L : Logic} {φ φ₁ φ₂ ψ ψ₁ ψ₂ χ ξ : Formula}

/-! ### Closure condition -/

/-- A logic closed under classical propositional reasoning. -/
class Cl (L : Logic) where
  mdp : ∀ {φ ψ : Formula}, φ 🡒 ψ ∈ L → φ ∈ L → ψ ∈ L
  implyK : ∀ (φ ψ : Formula), Axioms.ImplyK φ ψ ∈ L
  implyS : ∀ (φ ψ χ : Formula), Axioms.ImplyS φ ψ χ ∈ L
  dne : ∀ (φ : Formula), Axioms.DNE φ ∈ L
  andElim₁ : ∀ (φ ψ : Formula), Axioms.AndElim₁ φ ψ ∈ L
  andElim₂ : ∀ (φ ψ : Formula), Axioms.AndElim₂ φ ψ ∈ L
  andIntro : ∀ (φ ψ : Formula), Axioms.AndIntro φ ψ ∈ L
  orIntro₁ : ∀ (φ ψ : Formula), Axioms.OrIntro₁ φ ψ ∈ L
  orIntro₂ : ∀ (φ ψ : Formula), Axioms.OrIntro₂ φ ψ ∈ L
  orElim : ∀ (φ ψ χ : Formula), Axioms.OrElim φ ψ χ ∈ L

section

variable [L.Cl]

lemma mdp! : φ 🡒 ψ ∈ L → φ ∈ L → ψ ∈ L := Cl.mdp

@[inherit_doc] infixl:90 "⨀" => mdp!

@[simp] lemma implyK! : φ 🡒 ψ 🡒 φ ∈ L := Cl.implyK ..
@[simp] lemma implyS! : (φ 🡒 ψ 🡒 χ) 🡒 (φ 🡒 ψ) 🡒 φ 🡒 χ ∈ L := Cl.implyS ..
@[simp] lemma dne! : ∼∼φ 🡒 φ ∈ L := Cl.dne ..
@[simp] lemma and₁! : φ ⋏ ψ 🡒 φ ∈ L := Cl.andElim₁ ..
@[simp] lemma and₂! : φ ⋏ ψ 🡒 ψ ∈ L := Cl.andElim₂ ..
@[simp] lemma and₃! : φ 🡒 ψ 🡒 φ ⋏ ψ ∈ L := Cl.andIntro ..
@[simp] lemma or₁! : φ 🡒 φ ⋎ ψ ∈ L := Cl.orIntro₁ ..
@[simp] lemma or₂! : ψ 🡒 φ ⋎ ψ ∈ L := Cl.orIntro₂ ..
@[simp] lemma or₃! : (φ 🡒 χ) 🡒 (ψ 🡒 χ) 🡒 (φ ⋎ ψ) 🡒 χ ∈ L := Cl.orElim ..

/-! ### Implication -/

lemma C!_of_conseq! (h : φ ∈ L) : ψ 🡒 φ ∈ L := implyK! ⨀ h

alias dhyp! := C!_of_conseq!

@[simp] lemma C!_id : φ 🡒 φ ∈ L := implyS! (ψ := φ 🡒 φ) ⨀ implyK! ⨀ implyK!

@[grind →] lemma mdp₁! (hχ : φ 🡒 ψ 🡒 χ ∈ L) (hψ : φ 🡒 ψ ∈ L) : φ 🡒 χ ∈ L := implyS! ⨀ hχ ⨀ hψ

@[inherit_doc] infixl:90 "⨀₁" => mdp₁!

@[grind →]
lemma mdp₂! (hξ : φ 🡒 ψ 🡒 χ 🡒 ξ ∈ L) (hχ : φ 🡒 ψ 🡒 χ ∈ L) : φ 🡒 ψ 🡒 ξ ∈ L :=
  C!_of_conseq! implyS! ⨀₁ hξ ⨀₁ hχ

@[inherit_doc] infixl:90 "⨀₂" => mdp₂!

@[grind →]
lemma mdp₃! {ζ} (hζ : φ 🡒 ψ 🡒 χ 🡒 ξ 🡒 ζ ∈ L) (hξ : φ 🡒 ψ 🡒 χ 🡒 ξ ∈ L) :
    φ 🡒 ψ 🡒 χ 🡒 ζ ∈ L :=
  C!_of_conseq! (C!_of_conseq! implyS!) ⨀₂ hζ ⨀₂ hξ

@[inherit_doc] infixl:90 "⨀₃" => mdp₃!

@[grind →]
lemma mdp₄! {ζ ζ'} (hζ' : φ 🡒 ψ 🡒 χ 🡒 ξ 🡒 ζ 🡒 ζ' ∈ L) (hζ : φ 🡒 ψ 🡒 χ 🡒 ξ 🡒 ζ ∈ L) :
    φ 🡒 ψ 🡒 χ 🡒 ξ 🡒 ζ' ∈ L :=
  C!_of_conseq! (C!_of_conseq! (C!_of_conseq! implyS!)) ⨀₃ hζ' ⨀₃ hζ

@[inherit_doc] infixl:90 "⨀₄" => mdp₄!

@[grind <=]
lemma C!_trans (hψ : φ 🡒 ψ ∈ L) (hχ : ψ 🡒 χ ∈ L) : φ 🡒 χ ∈ L := mdp₁! (C!_of_conseq! hχ) hψ

lemma C!_swap (h : φ 🡒 ψ 🡒 χ ∈ L) : ψ 🡒 φ 🡒 χ ∈ L := C!_trans implyK! (implyS! ⨀ h)

@[grind .] lemma CCCC! : φ 🡒 ψ 🡒 χ 🡒 φ ∈ L := C!_trans implyK! implyK!

@[simp] lemma CCC! : (φ 🡒 ψ) 🡒 (ψ 🡒 χ) 🡒 (φ 🡒 χ) ∈ L := C!_swap (C!_trans implyK! implyS!)

lemma CCC!_of_C!_right (h : ψ 🡒 χ ∈ L) : (φ 🡒 ψ) 🡒 (φ 🡒 χ) ∈ L := implyS! ⨀ C!_of_conseq! h

lemma CCC!_of_C!_left (h : ψ 🡒 φ ∈ L) : (φ 🡒 χ) 🡒 (ψ 🡒 χ) ∈ L := CCC! ⨀ h

@[simp] lemma CCCCC! : (φ 🡒 ψ 🡒 χ) 🡒 (ψ 🡒 φ 🡒 χ) ∈ L := C!_trans implyS! (CCC!_of_C!_left implyK!)

@[simp] lemma verum! : (⊤ : Formula) ∈ L := C!_id

@[simp] lemma CV! : φ 🡒 ⊤ ∈ L := C!_of_conseq! verum!

/-! ### Negation -/

omit [L.Cl] in
@[grind =] lemma N!_iff_CO! : ∼φ ∈ L ↔ φ 🡒 ⊥ ∈ L := Iff.rfl

@[simp] lemma efq! : ⊥ 🡒 φ ∈ L := C!_trans implyK! dne!

@[grind ⇒] lemma of_O! (h : (⊥ : Formula) ∈ L) : φ ∈ L := efq! ⨀ h

@[simp] lemma NO! : ∼(⊥ : Formula) ∈ L := C!_id

@[grind ⇒] lemma of_NN! (h : ∼∼φ ∈ L) : φ ∈ L := dne! ⨀ h

@[simp] lemma dni! : φ 🡒 ∼∼φ ∈ L := C!_swap C!_id

lemma dni'! (h : φ ∈ L) : ∼∼φ ∈ L := dni! ⨀ h

@[simp] lemma CCNN! : (φ 🡒 ψ) 🡒 (∼ψ 🡒 ∼φ) ∈ L := CCC!

@[simp]
lemma elimContra! : (∼ψ 🡒 ∼φ) 🡒 (φ 🡒 ψ) ∈ L :=
  CCC!_of_C!_right (CCC!_of_C!_right dne!) ⨀ (CCC!_of_C!_right CCCCC! ⨀ C!_id)

lemma contra! (h : φ 🡒 ψ ∈ L) : ∼ψ 🡒 ∼φ ∈ L := CCNN! ⨀ h

lemma neg_mdp (hφ : ∼φ ∈ L) (h : φ ∈ L) : (⊥ : Formula) ∈ L := hφ ⨀ h

lemma explode! (h₁ : φ ∈ L) (h₂ : ∼φ ∈ L) : ψ ∈ L := of_O! <| neg_mdp h₂ h₁

@[simp] lemma CNC! : ∼φ 🡒 φ 🡒 ψ ∈ L := C!_swap CCC! ⨀ efq!

lemma C_of_N (h : ∼φ ∈ L) : φ 🡒 ψ ∈ L := CNC! ⨀ h

lemma CN!_of_CN!_left (h : ∼φ 🡒 ψ ∈ L) : ∼ψ 🡒 φ ∈ L := C!_trans (contra! h) dne!

lemma CN!_of_CN!_right (h : φ 🡒 ∼ψ ∈ L) : ψ 🡒 ∼φ ∈ L := C!_trans dni! (contra! h)

lemma C!_of_CNN! (h : ∼φ 🡒 ∼ψ ∈ L) : ψ 🡒 φ ∈ L := elimContra! ⨀ h

/-! ### Conjunction -/

@[grind ->] lemma K!_left (h : φ ⋏ ψ ∈ L) : φ ∈ L := and₁! ⨀ h

@[grind ->] lemma K!_right (h : φ ⋏ ψ ∈ L) : ψ ∈ L := and₂! ⨀ h

@[grind <-] lemma K!_intro (h₁ : φ ∈ L) (h₂ : ψ ∈ L) : φ ⋏ ψ ∈ L := and₃! ⨀ h₁ ⨀ h₂

@[grind =] lemma K!_intro_iff : φ ⋏ ψ ∈ L ↔ φ ∈ L ∧ ψ ∈ L :=
  ⟨fun h => ⟨K!_left h, K!_right h⟩, fun ⟨h₁, h₂⟩ => K!_intro h₁ h₂⟩

@[grind <=] lemma CK!_of_C!_of_C! (hψ : φ 🡒 ψ ∈ L) (hχ : φ 🡒 χ ∈ L) : φ 🡒 ψ ⋏ χ ∈ L :=
  mdp₁! (C!_trans hψ and₃!) hχ

alias right_K!_intro := CK!_of_C!_of_C!

@[simp, grind .] lemma CKK! : φ ⋏ ψ 🡒 ψ ⋏ φ ∈ L := CK!_of_C!_of_C! and₂! and₁!

@[grind <-] lemma K!_symm (h : φ ⋏ ψ ∈ L) : ψ ⋏ φ ∈ L := CKK! ⨀ h

@[simp, grind .]
lemma ECKCC! : (φ ⋏ ψ 🡒 χ) 🡘 (φ 🡒 ψ 🡒 χ) ∈ L :=
  K!_intro
    (C!_of_conseq! CCC! ⨀₁ C!_of_conseq! and₃! ⨀₁ (CCCCC! ⨀ CCC!))
    (C!_trans (CCC! ⨀ and₁!) (C!_swap implyS! ⨀ and₂!))

@[grind =] lemma CK!_iff_CC! : φ ⋏ ψ 🡒 χ ∈ L ↔ φ 🡒 ψ 🡒 χ ∈ L :=
  ⟨fun h => C!_trans and₃! (CCC!_of_C!_right h),
   fun h => mdp₁! (C!_trans and₁! h) and₂!⟩

@[simp] lemma CKNO! : φ ⋏ ∼φ 🡒 ⊥ ∈ L := CK!_iff_CC!.mpr dni!

lemma O!_intro_of_KN! (h : φ ⋏ ∼φ ∈ L) : (⊥ : Formula) ∈ L := CKNO! ⨀ h

/-! ### Disjunction -/

@[grind .] lemma A!_intro_left (h : φ ∈ L) : φ ⋎ ψ ∈ L := or₁! ⨀ h

@[grind .] lemma A!_intro_right (h : ψ ∈ L) : φ ⋎ ψ ∈ L := or₂! ⨀ h

lemma left_A!_intro (h₁ : φ 🡒 χ ∈ L) (h₂ : ψ 🡒 χ ∈ L) : φ ⋎ ψ 🡒 χ ∈ L := or₃! ⨀ h₁ ⨀ h₂

lemma of_C!_of_C!_of_A! (h₁ : φ 🡒 χ ∈ L) (h₂ : ψ 🡒 χ ∈ L) (h₃ : φ ⋎ ψ ∈ L) : χ ∈ L :=
  left_A!_intro h₁ h₂ ⨀ h₃

@[simp] lemma lem! : φ ⋎ ∼φ ∈ L := C!_id

/-! ### Biimplication -/

@[grind ←] lemma E!_intro (h₁ : φ 🡒 ψ ∈ L) (h₂ : ψ 🡒 φ ∈ L) : φ 🡘 ψ ∈ L := K!_intro h₁ h₂

@[simp] lemma E!_id : φ 🡘 φ ∈ L := E!_intro C!_id C!_id

@[grind →] lemma C_of_E_mp! (h : φ 🡘 ψ ∈ L) : φ 🡒 ψ ∈ L := K!_left h

@[grind →] lemma C_of_E_mpr! (h : φ 🡘 ψ ∈ L) : ψ 🡒 φ ∈ L := K!_right h

@[simp] lemma CEE! : (φ 🡘 ψ) 🡒 (ψ 🡘 φ) ∈ L := CKK!

@[grind <-] lemma E!_symm (h : φ 🡘 ψ ∈ L) : ψ 🡘 φ ∈ L := K!_symm h

@[grind <=] lemma E!_trans (h₁ : φ 🡘 ψ ∈ L) (h₂ : ψ 🡘 χ ∈ L) : φ 🡘 χ ∈ L :=
  E!_intro (C!_trans (C_of_E_mp! h₁) (C_of_E_mp! h₂)) (C!_trans (C_of_E_mpr! h₂) (C_of_E_mpr! h₁))

@[grind →] lemma iff_of_E! (h : φ 🡘 ψ ∈ L) : φ ∈ L ↔ ψ ∈ L :=
  ⟨fun hφ => C_of_E_mp! h ⨀ hφ, fun hψ => C_of_E_mpr! h ⨀ hψ⟩

lemma EKK!_of_E!_of_E! (h₁ : φ₁ 🡘 φ₂ ∈ L) (h₂ : ψ₁ 🡘 ψ₂ ∈ L) : φ₁ ⋏ ψ₁ 🡘 φ₂ ⋏ ψ₂ ∈ L :=
  E!_intro
    (CK!_of_C!_of_C! (C!_trans and₁! (C_of_E_mp! h₁)) (C!_trans and₂! (C_of_E_mp! h₂)))
    (CK!_of_C!_of_C! (C!_trans and₁! (C_of_E_mpr! h₁)) (C!_trans and₂! (C_of_E_mpr! h₂)))

end

end Logic

/-! ### Finite conjunction -/

/-- The conjunction of a finite set of formulas. -/
noncomputable def FormulaFinset.conj (s : FormulaFinset) : Formula := s.toList.foldr (· ⋏ ·) ⊤

namespace Logic

variable {L : Logic} [L.Cl] {φ ψ : Formula} {Γ Δ : FormulaFinset}

private lemma left_lconj!_intro {l : List Formula} (h : φ ∈ l) : l.foldr (· ⋏ ·) ⊤ 🡒 φ ∈ L := by
  induction l with
  | nil => simp at h;
  | cons ψ l ih =>
    rcases List.mem_cons.mp h with rfl | h;
    . exact and₁!;
    . exact C!_trans and₂! (ih h);

private lemma right_lconj!_intro {l : List Formula} (b : ∀ ψ ∈ l, φ 🡒 ψ ∈ L) :
    φ 🡒 l.foldr (· ⋏ ·) ⊤ ∈ L := by
  induction l with
  | nil => exact CV!;
  | cons ψ l ih => exact CK!_of_C!_of_C! (b ψ (by simp)) (ih fun χ hχ => b χ (by simp [hχ]));

@[simp] lemma left_Fconj!_intro (h : φ ∈ Γ) : Γ.conj 🡒 φ ∈ L :=
  left_lconj!_intro (Finset.mem_toList.mpr h)

lemma right_Fconj!_intro (b : ∀ ψ ∈ Γ, φ 🡒 ψ ∈ L) : φ 🡒 Γ.conj ∈ L :=
  right_lconj!_intro fun ψ hψ => b ψ (Finset.mem_toList.mp hψ)

lemma Fconj!_intro (b : ∀ ψ ∈ Γ, ψ ∈ L) : Γ.conj ∈ L :=
  right_Fconj!_intro (fun ψ hψ => C!_of_conseq! (b ψ hψ)) ⨀ verum!

@[grind =] lemma Fconj!_iff_forall_provable : Γ.conj ∈ L ↔ ∀ φ ∈ Γ, φ ∈ L :=
  ⟨fun h _ hφ => left_Fconj!_intro hφ ⨀ h, Fconj!_intro⟩

lemma CFconj!_Fconj! (h : Δ ⊆ Γ) : Γ.conj 🡒 Δ.conj ∈ L :=
  right_Fconj!_intro fun _ hψ => left_Fconj!_intro (h hψ)

lemma EFconjInsertKFconj! : (insert φ Γ).conj 🡘 (φ ⋏ Γ.conj) ∈ L := by
  apply E!_intro;
  . exact CK!_of_C!_of_C! (left_Fconj!_intro (by simp)) (CFconj!_Fconj! (by simp));
  . apply right_Fconj!_intro;
    intro ψ hψ;
    rcases Finset.mem_insert.mp hψ with rfl | hψ;
    . exact and₁!;
    . exact C!_trans and₂! (left_Fconj!_intro hψ);

@[simp] lemma CFconjUnionKFconj! : (Γ ∪ Δ).conj 🡒 Γ.conj ⋏ Δ.conj ∈ L :=
  CK!_of_C!_of_C! (CFconj!_Fconj! (by simp)) (CFconj!_Fconj! (by simp))

@[simp] lemma CKFconjFconjUnion! : Γ.conj ⋏ Δ.conj 🡒 (Γ ∪ Δ).conj ∈ L := by
  apply right_Fconj!_intro;
  intro ψ hψ;
  rcases Finset.mem_union.mp hψ with hψ | hψ;
  . exact C!_trans and₁! (left_Fconj!_intro hψ);
  . exact C!_trans and₂! (left_Fconj!_intro hψ);

end Logic

end LO.Modal

end
