module

public import Neighborhood.Logic.Cl

/-!
# Derivability from a set of assumptions

Derivability of `φ` from a set `T` of assumptions in a logic `L`, defined as provability in `L`
of an implication whose antecedent is the conjunction of a finite subset of `T`, together with
the deduction theorem and the resulting notion of a consistent set of formulas.
-/

@[expose] public section

namespace LO.Modal

/-- `φ` is derivable from the assumptions `T` in the logic `L`. -/
def Logic.CProvable (L : Logic) (T : FormulaSet) (φ : Formula) : Prop :=
  ∃ Γ : FormulaFinset, ↑Γ ⊆ T ∧ Γ.conj 🡒 φ ∈ L

@[inherit_doc] notation:45 T:46 " *⊢[" L "] " φ:46 => Logic.CProvable L T φ

/-- `φ` is not derivable from the assumptions `T` in the logic `L`. -/
abbrev Logic.CUnprovable (L : Logic) (T : FormulaSet) (φ : Formula) : Prop := ¬(T *⊢[L] φ)

@[inherit_doc] notation:45 T:46 " *⊬[" L "] " φ:46 => Logic.CUnprovable L T φ

namespace Logic.Context

variable {L : Logic} {T U : FormulaSet} {φ ψ χ : Formula}

@[grind =]
lemma iff_exists_finset : T *⊢[L] φ ↔ ∃ Γ : FormulaFinset, ↑Γ ⊆ T ∧ Γ.conj 🡒 φ ∈ L := Iff.rfl

lemma weakening! (hs : T ⊆ U) (h : T *⊢[L] φ) : U *⊢[L] φ := by
  obtain ⟨Γ, hΓ, hφ⟩ := h;
  exact ⟨Γ, hΓ.trans hs, hφ⟩;

section

variable [L.Cl]

/-- A theorem of `L` is derivable from any set of assumptions. -/
lemma of! (h : φ ∈ L) : T *⊢[L] φ := ⟨∅, by simp, C!_of_conseq! h⟩

/-- An assumption is derivable from itself. -/
lemma by_axm! (h : φ ∈ T) : T *⊢[L] φ := ⟨{φ}, by simpa, left_Fconj!_intro (by simp)⟩

lemma mdp! (h₁ : T *⊢[L] φ 🡒 ψ) (h₂ : T *⊢[L] φ) : T *⊢[L] ψ := by
  obtain ⟨Γ₁, hΓ₁, h₁⟩ := h₁;
  obtain ⟨Γ₂, hΓ₂, h₂⟩ := h₂;
  refine ⟨Γ₁ ∪ Γ₂, ?_, ?_⟩;
  . simp only [Finset.coe_union];
    exact Set.union_subset hΓ₁ hΓ₂;
  . exact mdp₁!
      (C!_trans (C!_trans CFconjUnionKFconj! and₁!) h₁)
      (C!_trans (C!_trans CFconjUnionKFconj! and₂!) h₂);

lemma deductInv! (h : T *⊢[L] φ 🡒 ψ) : insert φ T *⊢[L] ψ :=
  mdp! (weakening! (Set.subset_insert _ _) h) (by_axm! (Set.mem_insert _ _))

lemma deduct! (h : insert φ T *⊢[L] ψ) : T *⊢[L] φ 🡒 ψ := by
  obtain ⟨Γ, hΓ, hψ⟩ := h;
  refine ⟨Γ.erase φ, ?_, ?_⟩;
  . intro x hx;
    simp only [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff] at hx;
    have := hΓ hx.1;
    grind;
  . have h₁ : (insert φ (Γ.erase φ) : FormulaFinset).conj 🡒 ψ ∈ L := by
      apply C!_trans ?_ hψ;
      apply CFconj!_Fconj!;
      intro x hx;
      simp only [Finset.mem_insert, Finset.mem_erase];
      grind;
    exact C!_swap <| CK!_iff_CC!.mp <| C!_trans (C_of_E_mpr! EFconjInsertKFconj!) h₁;

@[grind =] lemma iff_deduct! : insert φ T *⊢[L] ψ ↔ T *⊢[L] φ 🡒 ψ := ⟨deduct!, deductInv!⟩

@[grind =] lemma iff_provable_empty : ∅ *⊢[L] φ ↔ φ ∈ L := by
  constructor;
  . rintro ⟨Γ, hΓ, hφ⟩;
    replace hΓ : Γ = ∅ := by simpa [Finset.coe_eq_empty] using hΓ;
    subst hΓ;
    exact hφ ⨀ (by simp [FormulaFinset.conj]);
  . apply of!;

/-- Transfer of a unary rule of `L` to derivability from assumptions. -/
lemma of_C! (hL : φ 🡒 ψ ∈ L) (h : T *⊢[L] φ) : T *⊢[L] ψ := mdp! (of! hL) h

/-- Transfer of a binary rule of `L` to derivability from assumptions. -/
lemma of_C!_of_C! (hL : φ 🡒 ψ 🡒 χ ∈ L) (h₁ : T *⊢[L] φ) (h₂ : T *⊢[L] ψ) : T *⊢[L] χ :=
  mdp! (of_C! hL h₁) h₂

end

end Logic.Context

namespace FormulaSet

open Logic Logic.Context

variable {L : Logic} {T : FormulaSet} {φ : Formula}

/-- `⊥` is not derivable from `T` in `L`. -/
abbrev Consistent (L : Logic) (T : FormulaSet) : Prop := T *⊬[L] ⊥

/-- `⊥` is derivable from `T` in `L`. -/
abbrev Inconsistent (L : Logic) (T : FormulaSet) : Prop := ¬(Consistent L T)

@[grind =] lemma iff_inconsistent : Inconsistent L T ↔ T *⊢[L] ⊥ := not_not

lemma def_consistent :
    Consistent L T ↔ ∀ Γ : FormulaFinset, ↑Γ ⊆ T → Γ.conj 🡒 ⊥ ∉ L := by
  constructor;
  . intro h Γ hΓ hC;
    exact h ⟨Γ, hΓ, hC⟩;
  . rintro h ⟨Γ, hΓ, hC⟩;
    exact h Γ hΓ hC;

lemma def_inconsistent :
    Inconsistent L T ↔ ∃ Γ : FormulaFinset, ↑Γ ⊆ T ∧ Γ.conj 🡒 ⊥ ∈ L := iff_inconsistent

section

variable [L.Cl]

lemma emptyset_consistent [L.Consistent] : Consistent L (∅ : FormulaSet) := by
  simpa [Consistent] using iff_provable_empty (L := L) (φ := ⊥) |>.not.mpr Logic.not_mem_falsum;

lemma not_mem_falsum_of_consistent (h : Consistent L T) : ⊥ ∉ T := fun hC => h (by_axm! hC)

lemma unprovable_either (h : Consistent L T) : ¬(T *⊢[L] φ ∧ T *⊢[L] ∼φ) := by
  rintro ⟨h₁, h₂⟩;
  exact h <| mdp! h₂ h₁;

lemma provable_iff_insert_neg_not_consistent :
    Inconsistent L (insert (∼φ) T) ↔ T *⊢[L] φ := by
  constructor;
  . intro h;
    exact of_C! dne! <| deduct! <| not_not.mp h;
  . intro h hC;
    exact hC <| deductInv! <| of_C! dni! h;

lemma unprovable_iff_insert_neg_consistent :
    Consistent L (insert (∼φ) T) ↔ T *⊬[L] φ := by
  simpa using provable_iff_insert_neg_not_consistent (L := L) (T := T) (φ := φ) |>.not;

lemma unprovable_iff_singleton_neg_consistent : Consistent L {∼φ} ↔ φ ∉ L := by
  rw [show ({∼φ} : FormulaSet) = insert (∼φ) ∅ by simp];
  exact unprovable_iff_insert_neg_consistent.trans iff_provable_empty.not

lemma either_consistent (h : Consistent L T) (φ) :
    Consistent L (insert φ T) ∨ Consistent L (insert (∼φ) T) := by
  by_contra hC;
  push Not at hC;
  obtain ⟨hC₁, hC₂⟩ := hC;
  replace hC₁ : T *⊢[L] ∼φ := deduct! hC₁;
  replace hC₂ : T *⊢[L] φ := provable_iff_insert_neg_not_consistent.mp (not_not.mpr hC₂);
  exact h <| mdp! hC₁ hC₂;

end

end FormulaSet

end LO.Modal

end
