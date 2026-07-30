module

public import Neighborhood.Formula.Basic

/-!
# Subformulas

The finite set of subformulas of a formula, and the notion of a subformula-closed set of
formulas.
-/

@[expose] public section

variable {α : Type u}

/-- The finite set of subformulas of a formula, including the formula itself. -/
@[grind =]
def Formula.subformulas [DecidableEq α] : Formula α → FormulaFinset α
  | atom a => {atom a}
  | ⊥      => {⊥}
  | A 🡒 B  => insert (A 🡒 B) (A.subformulas ∪ B.subformulas)
  | □A     => insert (□A) A.subformulas

namespace Formula.subformulas

variable [DecidableEq α] {A B C : Formula α}

@[simp, grind .] lemma mem_self : A ∈ A.subformulas := by induction A <;> simp [subformulas]

@[grind ⇒]
protected lemma mem_imp (h : (B 🡒 C) ∈ A.subformulas) :
    B ∈ A.subformulas ∧ C ∈ A.subformulas := by
  induction A with
  | himp B C ihB ihC =>
    simp only [subformulas, Finset.mem_insert, Finset.mem_union] at h;
    rcases h with ⟨rfl, rfl⟩ | h | h <;> simp_all [subformulas];
  | _ => simp_all [subformulas];

@[grind ⇒]
protected lemma mem_box (h : □B ∈ A.subformulas) : B ∈ A.subformulas := by
  induction A with
  | hbox B ihB =>
    simp only [subformulas, Finset.mem_insert, inj_box] at h ⊢;
    rcases h with rfl | h <;> simp_all;
  | himp B C ihB ihC =>
    simp_all only [subformulas, Finset.mem_insert, reduceCtorEq, Finset.mem_union, false_or];
    grind;
  | _ => simp_all [subformulas];

@[grind ⇒]
protected lemma mem_neg (h : (∼B) ∈ A.subformulas) :
    B ∈ A.subformulas ∧ ⊥ ∈ A.subformulas := subformulas.mem_imp h

@[grind ⇒]
protected lemma mem_and (h : (B ⋏ C) ∈ A.subformulas) :
    B ∈ A.subformulas ∧ C ∈ A.subformulas := by grind

@[grind ⇒]
protected lemma mem_or (h : (B ⋎ C) ∈ A.subformulas) :
    B ∈ A.subformulas ∧ C ∈ A.subformulas := by grind

lemma complexity_lower (h : B ∈ A.subformulas) : B.complexity ≤ A.complexity := by
  induction A with
  | hfalsum => simp_all [subformulas, complexity];
  | hatom => simp_all [subformulas, complexity];
  | hbox A ihA =>
    simp only [subformulas, Finset.mem_insert] at h;
    rcases h with rfl | h;
    . rfl;
    . simp_all [complexity];
      omega;
  | himp A₁ A₂ ihA₁ ihA₂ =>
    simp only [subformulas, Finset.mem_insert, Finset.mem_union] at h;
    rcases h with rfl | h | h;
    . rfl;
    . simp [complexity];
      have := ihA₁ h;
      omega;
    . simp [complexity];
      have := ihA₂ h;
      omega;

lemma subset_of_mem (hB : B ∈ A.subformulas) : B.subformulas ⊆ A.subformulas := by
  intro C hC;
  induction B with
  | hatom => simp_all [Formula.subformulas];
  | hfalsum => simp_all [Formula.subformulas];
  | himp B₁ B₂ ihB₁ ihB₂ =>
    simp only [subformulas, Finset.mem_insert, Finset.mem_union] at hC;
    rcases hC with rfl | hC | hC <;> grind;
  | hbox B ihB =>
    simp only [subformulas, Finset.mem_insert] at hC;
    rcases hC with rfl | hC <;> grind;

end Formula.subformulas

/-- A set of formulas is subformula-closed when it contains all subformulas of its members. -/
def FormulaSet.SubformulaClosed [DecidableEq α] (Γ : FormulaSet α) : Prop :=
  ∀ A ∈ Γ, ↑A.subformulas ⊆ Γ

namespace FormulaSet.SubformulaClosed

variable [DecidableEq α] {A B : Formula α} {Γ : FormulaSet α}

lemma of_mem_imp₁ (h : SubformulaClosed Γ) : A 🡒 B ∈ Γ → A ∈ Γ := by
  intro hAB;
  apply @h _ hAB;
  dsimp [Formula.subformulas];
  grind;

lemma of_mem_imp₂ (h : SubformulaClosed Γ) : A 🡒 B ∈ Γ → B ∈ Γ := by
  intro hAB;
  apply @h _ hAB;
  dsimp [Formula.subformulas];
  grind;

lemma of_mem_box (h : SubformulaClosed Γ) : □A ∈ Γ → A ∈ Γ := by
  intro hA;
  apply @h _ hA;
  dsimp [Formula.subformulas];
  grind;

end FormulaSet.SubformulaClosed

/-- Typeclass carrying subformula-closedness of a set of formulas. -/
class FormulaSet.IsSubformulaClosed [DecidableEq α] (Γ : FormulaSet α) where
  closed : Γ.SubformulaClosed

namespace FormulaSet.IsSubformulaClosed

variable [DecidableEq α] {A B : Formula α} {Γ : FormulaSet α} [Γ.IsSubformulaClosed]

@[grind →] lemma of_mem_imp₁ : A 🡒 B ∈ Γ → A ∈ Γ := SubformulaClosed.of_mem_imp₁ IsSubformulaClosed.closed
@[grind →] lemma of_mem_imp₂ : A 🡒 B ∈ Γ → B ∈ Γ := SubformulaClosed.of_mem_imp₂ IsSubformulaClosed.closed
@[grind →] lemma of_mem_box : □A ∈ Γ → A ∈ Γ := SubformulaClosed.of_mem_box IsSubformulaClosed.closed

end FormulaSet.IsSubformulaClosed

instance [DecidableEq α] {A : Formula α} : FormulaSet.IsSubformulaClosed (α := α) ↑A.subformulas where
  closed := fun _ hB ↦ Formula.subformulas.subset_of_mem hB

end
