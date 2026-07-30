module

public import Neighborhood.Logic.Cl

/-!
# Derivability from a set of assumptions

Derivability of `A` from a set `T` of assumptions in a logic `L`, defined as provability in `L`
of an implication whose antecedent is the conjunction of a finite subset of `T`, together with
the deduction theorem and the resulting notion of a consistent set of formulas.
-/

@[expose] public section

variable {α : Type u}

/-- `A` is derivable from the assumptions `T` in the logic `L`. -/
def Logic.CProvable (L : Logic α) (T : FormulaSet α) (A : Formula α) : Prop :=
  ∃ Γ : FormulaFinset α, ↑Γ ⊆ T ∧ Γ.conj 🡒 A ∈ L

@[inherit_doc] notation:45 T:46 " *⊢[" L "] " A:46 => Logic.CProvable L T A

/-- `A` is not derivable from the assumptions `T` in the logic `L`. -/
abbrev Logic.CUnprovable (L : Logic α) (T : FormulaSet α) (A : Formula α) : Prop := ¬(T *⊢[L] A)

@[inherit_doc] notation:45 T:46 " *⊬[" L "] " A:46 => Logic.CUnprovable L T A

namespace Logic.Context

variable {L : Logic α} {T U : FormulaSet α} {A B C : Formula α}

@[grind =]
lemma iff_exists_finset : T *⊢[L] A ↔ ∃ Γ : FormulaFinset α, ↑Γ ⊆ T ∧ Γ.conj 🡒 A ∈ L := Iff.rfl

lemma weakening (hs : T ⊆ U) (h : T *⊢[L] A) : U *⊢[L] A := by
  obtain ⟨Γ, hΓ, hA⟩ := h;
  exact ⟨Γ, hΓ.trans hs, hA⟩;

section

variable [L.Cl]

/-- A theorem of `L` is derivable from any set of assumptions. -/
lemma of (h : A ∈ L) : T *⊢[L] A := ⟨∅, by simp, C_of_conseq h⟩

/-- An assumption is derivable from itself. -/
lemma by_axm (h : A ∈ T) : T *⊢[L] A := ⟨{A}, by simpa, left_Fconj_intro (by simp)⟩

variable [DecidableEq α]

lemma mdp (h₁ : T *⊢[L] A 🡒 B) (h₂ : T *⊢[L] A) : T *⊢[L] B := by
  obtain ⟨Γ₁, hΓ₁, h₁⟩ := h₁;
  obtain ⟨Γ₂, hΓ₂, h₂⟩ := h₂;
  refine ⟨Γ₁ ∪ Γ₂, ?_, ?_⟩;
  . simp only [Finset.coe_union];
    exact Set.union_subset hΓ₁ hΓ₂;
  . exact mdp₁
      (C_trans (C_trans CFconjUnionKFconj and₁) h₁)
      (C_trans (C_trans CFconjUnionKFconj and₂) h₂);

lemma deductInv (h : T *⊢[L] A 🡒 B) : insert A T *⊢[L] B :=
  mdp (weakening (Set.subset_insert _ _) h) (by_axm (Set.mem_insert _ _))

lemma deduct (h : insert A T *⊢[L] B) : T *⊢[L] A 🡒 B := by
  obtain ⟨Γ, hΓ, hB⟩ := h;
  refine ⟨Γ.erase A, ?_, ?_⟩;
  . intro x hx;
    simp only [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff] at hx;
    have := hΓ hx.1;
    grind;
  . have h₁ : (insert A (Γ.erase A) : FormulaFinset α).conj 🡒 B ∈ L := by
      apply C_trans ?_ hB;
      apply CFconj_Fconj;
      intro x hx;
      simp only [Finset.mem_insert, Finset.mem_erase];
      grind;
    exact C_swap <| CK_iff_CC.mp <| C_trans (C_of_E_mpr EFconjInsertKFconj) h₁;

@[grind =] lemma iff_deduct : insert A T *⊢[L] B ↔ T *⊢[L] A 🡒 B := ⟨deduct, deductInv⟩

omit [DecidableEq α] in
@[grind =] lemma iff_provable_empty : ∅ *⊢[L] A ↔ A ∈ L := by
  constructor;
  . rintro ⟨Γ, hΓ, hA⟩;
    replace hΓ : Γ = ∅ := by simpa [Finset.coe_eq_empty] using hΓ;
    subst hΓ;
    exact hA ⨀ (by simp [FormulaFinset.conj]);
  . apply of;

/-- Transfer of a unary rule of `L` to derivability from assumptions. -/
lemma of_C (hL : A 🡒 B ∈ L) (h : T *⊢[L] A) : T *⊢[L] B := mdp (of hL) h

/-- Transfer of a binary rule of `L` to derivability from assumptions. -/
lemma of_C_of_C (hL : A 🡒 B 🡒 C ∈ L) (h₁ : T *⊢[L] A) (h₂ : T *⊢[L] B) : T *⊢[L] C :=
  mdp (of_C hL h₁) h₂

end

end Logic.Context

namespace FormulaSet

open Logic Logic.Context

variable {L : Logic α} {T : FormulaSet α} {A : Formula α}

/-- `⊥` is not derivable from `T` in `L`. -/
abbrev Consistent (L : Logic α) (T : FormulaSet α) : Prop := T *⊬[L] ⊥

/-- `⊥` is derivable from `T` in `L`. -/
abbrev Inconsistent (L : Logic α) (T : FormulaSet α) : Prop := ¬(Consistent L T)

@[grind =] lemma iff_inconsistent : Inconsistent L T ↔ T *⊢[L] ⊥ := not_not

lemma def_consistent :
    Consistent L T ↔ ∀ Γ : FormulaFinset α, ↑Γ ⊆ T → Γ.conj 🡒 ⊥ ∉ L := by
  constructor;
  . intro h Γ hΓ hC;
    exact h ⟨Γ, hΓ, hC⟩;
  . rintro h ⟨Γ, hΓ, hC⟩;
    exact h Γ hΓ hC;

lemma def_inconsistent :
    Inconsistent L T ↔ ∃ Γ : FormulaFinset α, ↑Γ ⊆ T ∧ Γ.conj 🡒 ⊥ ∈ L := iff_inconsistent

section

variable [L.Cl] [DecidableEq α]

omit [DecidableEq α] in
lemma emptyset_consistent (hL : L.IsConsistent) : Consistent L (∅ : FormulaSet α) := by
  simpa [Consistent] using iff_provable_empty (L := L) (A := ⊥) |>.not.mpr hL;

omit [DecidableEq α] in
lemma not_mem_falsum_of_consistent (h : Consistent L T) : ⊥ ∉ T := fun hC => h (by_axm hC)

lemma unprovable_either (h : Consistent L T) : ¬(T *⊢[L] A ∧ T *⊢[L] ∼A) := by
  rintro ⟨h₁, h₂⟩;
  exact h <| mdp h₂ h₁;

lemma provable_iff_insert_neg_not_consistent :
    Inconsistent L (insert (∼A) T) ↔ T *⊢[L] A := by
  constructor;
  . intro h;
    exact of_C dne <| deduct <| not_not.mp h;
  . intro h hC;
    exact hC <| deductInv <| of_C dni h;

lemma unprovable_iff_insert_neg_consistent :
    Consistent L (insert (∼A) T) ↔ T *⊬[L] A := by
  simpa using provable_iff_insert_neg_not_consistent (L := L) (T := T) (A := A) |>.not;

lemma unprovable_iff_singleton_neg_consistent : Consistent L {∼A} ↔ A ∉ L := by
  rw [show ({∼A} : FormulaSet α) = insert (∼A) ∅ by simp];
  exact unprovable_iff_insert_neg_consistent.trans iff_provable_empty.not

lemma either_consistent (h : Consistent L T) (A) :
    Consistent L (insert A T) ∨ Consistent L (insert (∼A) T) := by
  by_contra hC;
  push Not at hC;
  obtain ⟨hC₁, hC₂⟩ := hC;
  replace hC₁ : T *⊢[L] ∼A := deduct hC₁;
  replace hC₂ : T *⊢[L] A := provable_iff_insert_neg_not_consistent.mp (not_not.mpr hC₂);
  exact h <| mdp hC₁ hC₂;

end

end FormulaSet

end
