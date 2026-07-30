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

@[grind <=] lemma C!_trans (hψ : φ 🡒 ψ ∈ L) (hχ : ψ 🡒 χ ∈ L) : φ 🡒 χ ∈ L := mdp₁! (C!_of_conseq! hχ) hψ

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

lemma C_of_N (h : ∼φ ∈ L) : φ 🡒 ψ ∈ L := C!_trans h efq!

lemma CN!_of_CN!_left (h : ∼φ 🡒 ψ ∈ L) : ∼ψ 🡒 φ ∈ L := C!_trans (contra! h) dne!

lemma CN!_of_CN!_right (h : φ 🡒 ∼ψ ∈ L) : ψ 🡒 ∼φ ∈ L := C!_trans dni! (contra! h)

lemma C!_of_CNN! (h : ∼φ 🡒 ∼ψ ∈ L) : ψ 🡒 φ ∈ L := elimContra! ⨀ h

/-! ### Conjunction -/

@[grind ->] lemma K!_left (h : φ ⋏ ψ ∈ L) : φ ∈ L := sorry

@[grind ->] lemma K!_right (h : φ ⋏ ψ ∈ L) : ψ ∈ L := sorry

@[grind <-] lemma K!_intro (h₁ : φ ∈ L) (h₂ : ψ ∈ L) : φ ⋏ ψ ∈ L := sorry

@[grind =] lemma K!_intro_iff : φ ⋏ ψ ∈ L ↔ φ ∈ L ∧ ψ ∈ L := sorry

@[simp, grind .] lemma CKK! : φ ⋏ ψ 🡒 ψ ⋏ φ ∈ L := sorry

@[grind <-] lemma K!_symm (h : φ ⋏ ψ ∈ L) : ψ ⋏ φ ∈ L := sorry

@[grind <=] lemma CK!_of_C!_of_C! (hψ : φ 🡒 ψ ∈ L) (hχ : φ 🡒 χ ∈ L) : φ 🡒 ψ ⋏ χ ∈ L := sorry

alias right_K!_intro := CK!_of_C!_of_C!

@[simp, grind .] lemma ECKCC! : (φ ⋏ ψ 🡒 χ) 🡘 (φ 🡒 ψ 🡒 χ) ∈ L := sorry

@[grind =] lemma CK!_iff_CC! : φ ⋏ ψ 🡒 χ ∈ L ↔ φ 🡒 ψ 🡒 χ ∈ L := sorry

@[simp] lemma CKNO! : φ ⋏ ∼φ 🡒 ⊥ ∈ L := sorry

lemma O!_intro_of_KN! (h : φ ⋏ ∼φ ∈ L) : (⊥ : Formula) ∈ L := sorry

/-! ### Disjunction -/

@[grind .] lemma A!_intro_left (h : φ ∈ L) : φ ⋎ ψ ∈ L := sorry

@[grind .] lemma A!_intro_right (h : ψ ∈ L) : φ ⋎ ψ ∈ L := sorry

lemma left_A!_intro (h₁ : φ 🡒 χ ∈ L) (h₂ : ψ 🡒 χ ∈ L) : φ ⋎ ψ 🡒 χ ∈ L := sorry

lemma of_C!_of_C!_of_A! (h₁ : φ 🡒 χ ∈ L) (h₂ : ψ 🡒 χ ∈ L) (h₃ : φ ⋎ ψ ∈ L) : χ ∈ L := sorry

@[simp] lemma lem! : φ ⋎ ∼φ ∈ L := sorry

/-! ### Biimplication -/

@[grind ←] lemma E!_intro (h₁ : φ 🡒 ψ ∈ L) (h₂ : ψ 🡒 φ ∈ L) : φ 🡘 ψ ∈ L := sorry

@[simp] lemma E!_id : φ 🡘 φ ∈ L := sorry

@[grind →] lemma C_of_E_mp! (h : φ 🡘 ψ ∈ L) : φ 🡒 ψ ∈ L := sorry

@[grind →] lemma C_of_E_mpr! (h : φ 🡘 ψ ∈ L) : ψ 🡒 φ ∈ L := sorry

@[simp] lemma CEE! : (φ 🡘 ψ) 🡒 (ψ 🡘 φ) ∈ L := sorry

@[grind <-] lemma E!_symm (h : φ 🡘 ψ ∈ L) : ψ 🡘 φ ∈ L := sorry

@[grind <=] lemma E!_trans (h₁ : φ 🡘 ψ ∈ L) (h₂ : ψ 🡘 χ ∈ L) : φ 🡘 χ ∈ L := sorry

@[grind →] lemma iff_of_E! (h : φ 🡘 ψ ∈ L) : φ ∈ L ↔ ψ ∈ L := sorry

lemma EKK!_of_E!_of_E! (h₁ : φ₁ 🡘 φ₂ ∈ L) (h₂ : ψ₁ 🡘 ψ₂ ∈ L) : φ₁ ⋏ ψ₁ 🡘 φ₂ ⋏ ψ₂ ∈ L := sorry

end

end Logic

/-! ### Finite conjunction -/

/-- The conjunction of a finite set of formulas. -/
noncomputable def FormulaFinset.conj (s : FormulaFinset) : Formula := s.toList.foldr (· ⋏ ·) ⊤

namespace Logic

variable {L : Logic} [L.Cl] {φ ψ : Formula} {Γ Δ : FormulaFinset}

@[simp] lemma left_Fconj!_intro (h : φ ∈ Γ) : Γ.conj 🡒 φ ∈ L := sorry

lemma right_Fconj!_intro (b : ∀ ψ ∈ Γ, φ 🡒 ψ ∈ L) : φ 🡒 Γ.conj ∈ L := sorry

lemma Fconj!_intro (b : ∀ ψ ∈ Γ, ψ ∈ L) : Γ.conj ∈ L := sorry

@[grind =] lemma Fconj!_iff_forall_provable : Γ.conj ∈ L ↔ ∀ φ ∈ Γ, φ ∈ L := sorry

lemma CFconj!_Fconj! (h : Δ ⊆ Γ) : Γ.conj 🡒 Δ.conj ∈ L := sorry

lemma EFconjInsertKFconj! : (insert φ Γ).conj 🡘 (φ ⋏ Γ.conj) ∈ L := sorry

@[simp] lemma CFconjUnionKFconj! : (Γ ∪ Δ).conj 🡒 Γ.conj ⋏ Δ.conj ∈ L := sorry

@[simp] lemma CKFconjFconjUnion! : Γ.conj ⋏ Δ.conj 🡒 (Γ ∪ Δ).conj ∈ L := sorry

end Logic

end LO.Modal

end
