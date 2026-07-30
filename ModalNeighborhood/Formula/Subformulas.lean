module

public import ModalNeighborhood.Formula.Basic
public import ModalNeighborhood.Vorspiel

/-!
# Subformulas

The finite set of subformulas of a formula, and the notion of a subformula-closed set of
formulas.
-/

@[expose] public section

namespace LO.Modal

/-- The finite set of subformulas of a formula, including the formula itself. -/
@[grind =]
def Formula.subformulas : Formula → FormulaFinset
  | atom a => {atom a}
  | ⊥      => {⊥}
  | φ 🡒 ψ  => insert (φ 🡒 ψ) (φ.subformulas ∪ ψ.subformulas)
  | □φ     => insert (□φ) φ.subformulas

namespace Formula.subformulas

variable {φ ψ χ : Formula}

@[simp, grind .] lemma mem_self : φ ∈ φ.subformulas := by induction φ <;> simp [subformulas]

@[grind ⇒]
protected lemma mem_imp (h : (ψ 🡒 χ) ∈ φ.subformulas) :
    ψ ∈ φ.subformulas ∧ χ ∈ φ.subformulas := by
  induction φ with
  | himp ψ χ ihψ ihχ =>
    simp only [subformulas, Finset.mem_insert, Finset.mem_union] at h;
    rcases h with ⟨rfl, rfl⟩ | h | h <;> simp_all [subformulas];
  | _ => simp_all [subformulas];

@[grind ⇒]
protected lemma mem_box (h : □ψ ∈ φ.subformulas) : ψ ∈ φ.subformulas := by
  induction φ with
  | hbox ψ ihψ =>
    simp only [subformulas, Finset.mem_insert, inj_box] at h ⊢;
    rcases h with rfl | h <;> simp_all;
  | himp ψ χ ihψ ihχ =>
    simp_all only [subformulas, Finset.mem_insert, reduceCtorEq, Finset.mem_union, false_or];
    grind;
  | _ => simp_all [subformulas];

@[grind ⇒]
protected lemma mem_neg (h : (∼ψ) ∈ φ.subformulas) :
    ψ ∈ φ.subformulas ∧ ⊥ ∈ φ.subformulas := subformulas.mem_imp h

@[grind ⇒]
protected lemma mem_and (h : (ψ ⋏ χ) ∈ φ.subformulas) :
    ψ ∈ φ.subformulas ∧ χ ∈ φ.subformulas := by grind

@[grind ⇒]
protected lemma mem_or (h : (ψ ⋎ χ) ∈ φ.subformulas) :
    ψ ∈ φ.subformulas ∧ χ ∈ φ.subformulas := by grind

lemma complexity_lower (h : ψ ∈ φ.subformulas) : ψ.complexity ≤ φ.complexity := by
  induction φ with
  | hfalsum => simp_all [subformulas, complexity];
  | hatom => simp_all [subformulas, complexity];
  | hbox φ ihφ =>
    simp only [subformulas, Finset.mem_insert] at h;
    rcases h with rfl | h;
    . rfl;
    . simp_all [complexity];
      omega;
  | himp φ₁ φ₂ ihφ₁ ihφ₂ =>
    simp only [subformulas, Finset.mem_insert, Finset.mem_union] at h;
    rcases h with rfl | h | h;
    . rfl;
    . simp [complexity];
      have := ihφ₁ h;
      omega;
    . simp [complexity];
      have := ihφ₂ h;
      omega;

lemma subset_of_mem (hψ : ψ ∈ φ.subformulas) : ψ.subformulas ⊆ φ.subformulas := by
  intro ξ hξ;
  induction ψ with
  | hatom => simp_all [Formula.subformulas];
  | hfalsum => simp_all [Formula.subformulas];
  | himp ψ₁ ψ₂ ihψ₁ ihψ₂ =>
    simp only [subformulas, Finset.mem_insert, Finset.mem_union] at hξ;
    rcases hξ with rfl | hξ | hξ <;> grind;
  | hbox ψ ihψ =>
    simp only [subformulas, Finset.mem_insert] at hξ;
    rcases hξ with rfl | hξ <;> grind;

end Formula.subformulas

/-- A set of formulas is subformula-closed when it contains all subformulas of its members. -/
def FormulaSet.SubformulaClosed (Γ : FormulaSet) : Prop := ∀ φ ∈ Γ, φ.subformulas.toSet ⊆ Γ

namespace FormulaSet.SubformulaClosed

variable {φ ψ : Formula} {Γ : FormulaSet}

lemma of_mem_imp₁ (h : SubformulaClosed Γ) : φ 🡒 ψ ∈ Γ → φ ∈ Γ := by
  intro hφψ;
  apply @h _ hφψ;
  dsimp [Formula.subformulas];
  grind;

lemma of_mem_imp₂ (h : SubformulaClosed Γ) : φ 🡒 ψ ∈ Γ → ψ ∈ Γ := by
  intro hφψ;
  apply @h _ hφψ;
  dsimp [Formula.subformulas];
  grind;

lemma of_mem_box (h : SubformulaClosed Γ) : □φ ∈ Γ → φ ∈ Γ := by
  intro hφ;
  apply @h _ hφ;
  dsimp [Formula.subformulas];
  grind;

end FormulaSet.SubformulaClosed

/-- Typeclass carrying subformula-closedness of a set of formulas. -/
class FormulaSet.IsSubformulaClosed (Γ : FormulaSet) where
  closed : Γ.SubformulaClosed

namespace FormulaSet.IsSubformulaClosed

variable {φ ψ : Formula} {Γ : FormulaSet} [Γ.IsSubformulaClosed]

lemma of_mem_imp₁ : φ 🡒 ψ ∈ Γ → φ ∈ Γ := SubformulaClosed.of_mem_imp₁ IsSubformulaClosed.closed
lemma of_mem_imp₂ : φ 🡒 ψ ∈ Γ → ψ ∈ Γ := SubformulaClosed.of_mem_imp₂ IsSubformulaClosed.closed
lemma of_mem_box : □φ ∈ Γ → φ ∈ Γ := SubformulaClosed.of_mem_box IsSubformulaClosed.closed

end FormulaSet.IsSubformulaClosed

instance {φ : Formula} : FormulaSet.IsSubformulaClosed φ.subformulas.toSet where
  closed := fun _ hψ ↦ Formula.subformulas.subset_of_mem hψ

end LO.Modal

end
