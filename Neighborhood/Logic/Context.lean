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

lemma weakening! (hs : T ⊆ U) (h : T *⊢[L] φ) : U *⊢[L] φ := sorry

section

variable [L.Cl]

/-- A theorem of `L` is derivable from any set of assumptions. -/
lemma of! (h : φ ∈ L) : T *⊢[L] φ := sorry

/-- An assumption is derivable from itself. -/
lemma by_axm! (h : φ ∈ T) : T *⊢[L] φ := sorry

lemma mdp! (h₁ : T *⊢[L] φ 🡒 ψ) (h₂ : T *⊢[L] φ) : T *⊢[L] ψ := sorry

lemma deductInv! (h : T *⊢[L] φ 🡒 ψ) : insert φ T *⊢[L] ψ := sorry

lemma deduct! (h : insert φ T *⊢[L] ψ) : T *⊢[L] φ 🡒 ψ := sorry

@[grind =] lemma iff_deduct! : insert φ T *⊢[L] ψ ↔ T *⊢[L] φ 🡒 ψ := ⟨deduct!, deductInv!⟩

@[grind =] lemma iff_provable_empty : ∅ *⊢[L] φ ↔ φ ∈ L := sorry

/-- Transfer of a unary rule of `L` to derivability from assumptions. -/
lemma of_C! (hL : φ 🡒 ψ ∈ L) (h : T *⊢[L] φ) : T *⊢[L] ψ := sorry

/-- Transfer of a binary rule of `L` to derivability from assumptions. -/
lemma of_C!_of_C! (hL : φ 🡒 ψ 🡒 χ ∈ L) (h₁ : T *⊢[L] φ) (h₂ : T *⊢[L] ψ) : T *⊢[L] χ := sorry

end

end Logic.Context

namespace FormulaSet

open Logic Logic.Context

variable {L : Logic} {T : FormulaSet} {φ : Formula}

/-- `⊥` is not derivable from `T` in `L`. -/
abbrev Consistent (L : Logic) (T : FormulaSet) : Prop := T *⊬[L] ⊥

/-- `⊥` is derivable from `T` in `L`. -/
abbrev Inconsistent (L : Logic) (T : FormulaSet) : Prop := ¬(Consistent L T)

lemma def_consistent :
    Consistent L T ↔ ∀ Γ : FormulaFinset, ↑Γ ⊆ T → Γ.conj 🡒 ⊥ ∉ L := sorry

lemma def_inconsistent :
    Inconsistent L T ↔ ∃ Γ : FormulaFinset, ↑Γ ⊆ T ∧ Γ.conj 🡒 ⊥ ∈ L := sorry

section

variable [L.Cl]

lemma emptyset_consistent [L.Consistent] : Consistent L (∅ : FormulaSet) := sorry

lemma not_mem_falsum_of_consistent (h : Consistent L T) : ⊥ ∉ T := sorry

lemma unprovable_either (h : Consistent L T) : ¬(T *⊢[L] φ ∧ T *⊢[L] ∼φ) := sorry

lemma provable_iff_insert_neg_not_consistent :
    Inconsistent L (insert (∼φ) T) ↔ T *⊢[L] φ := sorry

lemma unprovable_iff_insert_neg_consistent :
    Consistent L (insert (∼φ) T) ↔ T *⊬[L] φ := sorry

lemma unprovable_iff_singleton_neg_consistent : Consistent L {∼φ} ↔ φ ∉ L := sorry

lemma either_consistent (h : Consistent L T) (φ) :
    Consistent L (insert φ T) ∨ Consistent L (insert (∼φ) T) := sorry

end

end FormulaSet

end LO.Modal

end
