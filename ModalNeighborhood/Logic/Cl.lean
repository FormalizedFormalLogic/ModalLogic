module

public import ModalNeighborhood.Logic.Basic

/-!
# Classical propositional reasoning inside a logic

Closure conditions of a logic under the Łukasiewicz axiomatisation of classical propositional
logic (`ImplyK`, `ImplyS`, `ElimContra` and modus ponens), and the derived toolkit of
propositional inferences. Since negation, conjunction, disjunction and biimplication are
abbreviations for implications and `⊥`, the toolkit is stated directly in terms of them.
-/

@[expose] public section

namespace LO.Modal

namespace Logic

variable {L : Logic} {φ φ₁ φ₂ ψ ψ₁ ψ₂ χ ξ : Formula}

/-! ### Closure conditions -/

/-- Closure of a logic under modus ponens. -/
class ModusPonens (L : Logic) where
  mdp : ∀ {φ ψ : Formula}, L ⊢ φ 🡒 ψ → L ⊢ φ → L ⊢ ψ

/-- A logic containing the axiom scheme `ImplyK`. -/
class HasImplyK (L : Logic) where
  implyK : ∀ (φ ψ : Formula), L ⊢ Axioms.ImplyK φ ψ

/-- A logic containing the axiom scheme `ImplyS`. -/
class HasImplyS (L : Logic) where
  implyS : ∀ (φ ψ χ : Formula), L ⊢ Axioms.ImplyS φ ψ χ

/-- A logic containing the axiom scheme `ElimContra`. -/
class HasElimContra (L : Logic) where
  elimContra : ∀ (φ ψ : Formula), L ⊢ Axioms.ElimContra φ ψ

/-- A logic closed under classical propositional reasoning. -/
class Cl (L : Logic) extends L.ModusPonens, L.HasImplyK, L.HasImplyS, L.HasElimContra

lemma mdp! [L.ModusPonens] : L ⊢ φ 🡒 ψ → L ⊢ φ → L ⊢ ψ := ModusPonens.mdp

@[inherit_doc] infixl:90 "⨀" => mdp!

@[simp] lemma implyK! [L.HasImplyK] : L ⊢ φ 🡒 ψ 🡒 φ := HasImplyK.implyK ..

@[simp] lemma implyS! [L.HasImplyS] : L ⊢ (φ 🡒 ψ 🡒 χ) 🡒 (φ 🡒 ψ) 🡒 φ 🡒 χ := HasImplyS.implyS ..

@[simp] lemma elimContra! [L.HasElimContra] : L ⊢ (∼ψ 🡒 ∼φ) 🡒 (φ 🡒 ψ) := HasElimContra.elimContra ..

section

variable [L.Cl]

/-! ### Implication -/

lemma C!_of_conseq! (h : L ⊢ φ) : L ⊢ ψ 🡒 φ := sorry

alias dhyp! := C!_of_conseq!

@[simp] lemma C!_id : L ⊢ φ 🡒 φ := sorry

@[grind →] lemma mdp₁! (hχ : L ⊢ φ 🡒 ψ 🡒 χ) (hψ : L ⊢ φ 🡒 ψ) : L ⊢ φ 🡒 χ := sorry

@[inherit_doc] infixl:90 "⨀₁" => mdp₁!

@[grind →]
lemma mdp₂! (hξ : L ⊢ φ 🡒 ψ 🡒 χ 🡒 ξ) (hχ : L ⊢ φ 🡒 ψ 🡒 χ) : L ⊢ φ 🡒 ψ 🡒 ξ := sorry

@[inherit_doc] infixl:90 "⨀₂" => mdp₂!

@[grind →]
lemma mdp₃! {ζ} (hζ : L ⊢ φ 🡒 ψ 🡒 χ 🡒 ξ 🡒 ζ) (hξ : L ⊢ φ 🡒 ψ 🡒 χ 🡒 ξ) :
    L ⊢ φ 🡒 ψ 🡒 χ 🡒 ζ := sorry

@[inherit_doc] infixl:90 "⨀₃" => mdp₃!

@[grind →]
lemma mdp₄! {ζ ζ'} (hζ' : L ⊢ φ 🡒 ψ 🡒 χ 🡒 ξ 🡒 ζ 🡒 ζ') (hζ : L ⊢ φ 🡒 ψ 🡒 χ 🡒 ξ 🡒 ζ) :
    L ⊢ φ 🡒 ψ 🡒 χ 🡒 ξ 🡒 ζ' := sorry

@[inherit_doc] infixl:90 "⨀₄" => mdp₄!

@[grind <=] lemma C!_trans (hψ : L ⊢ φ 🡒 ψ) (hχ : L ⊢ ψ 🡒 χ) : L ⊢ φ 🡒 χ := sorry

lemma C!_swap (h : L ⊢ φ 🡒 ψ 🡒 χ) : L ⊢ ψ 🡒 φ 🡒 χ := sorry

@[grind .] lemma CCCC! : L ⊢ φ 🡒 ψ 🡒 χ 🡒 φ := sorry

@[simp] lemma CCC! : L ⊢ (φ 🡒 ψ) 🡒 (ψ 🡒 χ) 🡒 (φ 🡒 χ) := sorry

lemma CCC!_of_C!_right (h : L ⊢ ψ 🡒 χ) : L ⊢ (φ 🡒 ψ) 🡒 (φ 🡒 χ) := sorry

lemma CCC!_of_C!_left (h : L ⊢ ψ 🡒 φ) : L ⊢ (φ 🡒 χ) 🡒 (ψ 🡒 χ) := sorry

@[simp] lemma verum! : L ⊢ ⊤ := sorry

@[simp] lemma CV! : L ⊢ φ 🡒 ⊤ := sorry

/-! ### Negation -/

@[grind =] lemma N!_iff_CO! : L ⊢ ∼φ ↔ L ⊢ φ 🡒 ⊥ := Iff.rfl

@[simp] lemma efq! : L ⊢ ⊥ 🡒 φ := sorry

@[grind ⇒] lemma of_O! (h : L ⊢ ⊥) : L ⊢ φ := sorry

@[simp] lemma NO! : L ⊢ ∼(⊥ : Formula) := sorry

@[simp] lemma dne! : L ⊢ ∼∼φ 🡒 φ := sorry

@[grind ⇒] lemma of_NN! (h : L ⊢ ∼∼φ) : L ⊢ φ := sorry

@[simp] lemma dni! : L ⊢ φ 🡒 ∼∼φ := sorry

lemma dni'! (h : L ⊢ φ) : L ⊢ ∼∼φ := sorry

@[simp] lemma CCNN! : L ⊢ (φ 🡒 ψ) 🡒 (∼ψ 🡒 ∼φ) := sorry

lemma contra! (h : L ⊢ φ 🡒 ψ) : L ⊢ ∼ψ 🡒 ∼φ := sorry

lemma explode! (h₁ : L ⊢ φ) (h₂ : L ⊢ ∼φ) : L ⊢ ψ := sorry

lemma neg_mdp (hφ : L ⊢ ∼φ) (h : L ⊢ φ) : L ⊢ ⊥ := sorry

lemma C_of_N (h : L ⊢ ∼φ) : L ⊢ φ 🡒 ψ := sorry

lemma CN!_of_CN!_left (h : L ⊢ ∼φ 🡒 ψ) : L ⊢ ∼ψ 🡒 φ := sorry

lemma CN!_of_CN!_right (h : L ⊢ φ 🡒 ∼ψ) : L ⊢ ψ 🡒 ∼φ := sorry

lemma C!_of_CNN! (h : L ⊢ ∼φ 🡒 ∼ψ) : L ⊢ ψ 🡒 φ := sorry

/-! ### Conjunction -/

@[simp] lemma and₁! : L ⊢ φ ⋏ ψ 🡒 φ := sorry

@[simp] lemma and₂! : L ⊢ φ ⋏ ψ 🡒 ψ := sorry

@[simp] lemma and₃! : L ⊢ φ 🡒 ψ 🡒 φ ⋏ ψ := sorry

@[grind ->] lemma K!_left (h : L ⊢ φ ⋏ ψ) : L ⊢ φ := sorry

@[grind ->] lemma K!_right (h : L ⊢ φ ⋏ ψ) : L ⊢ ψ := sorry

@[grind <-] lemma K!_intro (h₁ : L ⊢ φ) (h₂ : L ⊢ ψ) : L ⊢ φ ⋏ ψ := sorry

@[grind =] lemma K!_intro_iff : L ⊢ φ ⋏ ψ ↔ L ⊢ φ ∧ L ⊢ ψ := sorry

@[simp, grind .] lemma CKK! : L ⊢ φ ⋏ ψ 🡒 ψ ⋏ φ := sorry

@[grind <-] lemma K!_symm (h : L ⊢ φ ⋏ ψ) : L ⊢ ψ ⋏ φ := sorry

@[grind <=] lemma CK!_of_C!_of_C! (hψ : L ⊢ φ 🡒 ψ) (hχ : L ⊢ φ 🡒 χ) : L ⊢ φ 🡒 ψ ⋏ χ := sorry

alias right_K!_intro := CK!_of_C!_of_C!

@[simp, grind .] lemma ECKCC! : L ⊢ (φ ⋏ ψ 🡒 χ) 🡘 (φ 🡒 ψ 🡒 χ) := sorry

@[grind =] lemma CK!_iff_CC! : L ⊢ φ ⋏ ψ 🡒 χ ↔ L ⊢ φ 🡒 ψ 🡒 χ := sorry

@[simp] lemma CKNO! : L ⊢ φ ⋏ ∼φ 🡒 ⊥ := sorry

lemma O!_intro_of_KN! (h : L ⊢ φ ⋏ ∼φ) : L ⊢ ⊥ := sorry

/-! ### Disjunction -/

@[simp] lemma or₁! : L ⊢ φ 🡒 φ ⋎ ψ := sorry

@[simp] lemma or₂! : L ⊢ ψ 🡒 φ ⋎ ψ := sorry

@[simp] lemma or₃! : L ⊢ (φ 🡒 χ) 🡒 (ψ 🡒 χ) 🡒 (φ ⋎ ψ) 🡒 χ := sorry

@[grind .] lemma A!_intro_left (h : L ⊢ φ) : L ⊢ φ ⋎ ψ := sorry

@[grind .] lemma A!_intro_right (h : L ⊢ ψ) : L ⊢ φ ⋎ ψ := sorry

lemma left_A!_intro (h₁ : L ⊢ φ 🡒 χ) (h₂ : L ⊢ ψ 🡒 χ) : L ⊢ φ ⋎ ψ 🡒 χ := sorry

lemma of_C!_of_C!_of_A! (h₁ : L ⊢ φ 🡒 χ) (h₂ : L ⊢ ψ 🡒 χ) (h₃ : L ⊢ φ ⋎ ψ) : L ⊢ χ := sorry

@[simp] lemma lem! : L ⊢ φ ⋎ ∼φ := sorry

/-! ### Biimplication -/

@[grind ←] lemma E!_intro (h₁ : L ⊢ φ 🡒 ψ) (h₂ : L ⊢ ψ 🡒 φ) : L ⊢ φ 🡘 ψ := sorry

@[simp] lemma E!_id : L ⊢ φ 🡘 φ := sorry

@[grind →] lemma C_of_E_mp! (h : L ⊢ φ 🡘 ψ) : L ⊢ φ 🡒 ψ := sorry

@[grind →] lemma C_of_E_mpr! (h : L ⊢ φ 🡘 ψ) : L ⊢ ψ 🡒 φ := sorry

@[simp] lemma CEE! : L ⊢ (φ 🡘 ψ) 🡒 (ψ 🡘 φ) := sorry

@[grind <-] lemma E!_symm (h : L ⊢ φ 🡘 ψ) : L ⊢ ψ 🡘 φ := sorry

@[grind <=] lemma E!_trans (h₁ : L ⊢ φ 🡘 ψ) (h₂ : L ⊢ ψ 🡘 χ) : L ⊢ φ 🡘 χ := sorry

@[grind →] lemma iff_of_E! (h : L ⊢ φ 🡘 ψ) : L ⊢ φ ↔ L ⊢ ψ := sorry

lemma EKK!_of_E!_of_E! (h₁ : L ⊢ φ₁ 🡘 φ₂) (h₂ : L ⊢ ψ₁ 🡘 ψ₂) : L ⊢ φ₁ ⋏ ψ₁ 🡘 φ₂ ⋏ ψ₂ := sorry

end

end Logic

/-! ### Finite conjunction -/

/-- The conjunction of a finite set of formulas. -/
noncomputable def FormulaFinset.conj (s : FormulaFinset) : Formula := s.toList.foldr (· ⋏ ·) ⊤

namespace Logic

variable {L : Logic} [L.Cl] {φ ψ : Formula} {Γ Δ : FormulaFinset}

@[simp] lemma left_Fconj!_intro (h : φ ∈ Γ) : L ⊢ Γ.conj 🡒 φ := sorry

lemma right_Fconj!_intro (b : ∀ ψ ∈ Γ, L ⊢ φ 🡒 ψ) : L ⊢ φ 🡒 Γ.conj := sorry

lemma Fconj!_intro (b : ∀ ψ ∈ Γ, L ⊢ ψ) : L ⊢ Γ.conj := sorry

@[grind =] lemma Fconj!_iff_forall_provable : L ⊢ Γ.conj ↔ ∀ φ ∈ Γ, L ⊢ φ := sorry

lemma CFconj!_Fconj! (h : Δ ⊆ Γ) : L ⊢ Γ.conj 🡒 Δ.conj := sorry

lemma EFconjInsertKFconj! : L ⊢ (insert φ Γ).conj 🡘 (φ ⋏ Γ.conj) := sorry

@[simp] lemma CFconjUnionKFconj! : L ⊢ (Γ ∪ Δ).conj 🡒 Γ.conj ⋏ Δ.conj := sorry

@[simp] lemma CKFconjFconjUnion! : L ⊢ Γ.conj ⋏ Δ.conj 🡒 (Γ ∪ Δ).conj := sorry

end Logic

end LO.Modal

end
