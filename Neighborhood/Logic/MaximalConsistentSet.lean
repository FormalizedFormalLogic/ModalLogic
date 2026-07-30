module

public import Mathlib.Order.Zorn
public import Neighborhood.Logic.Context
public import Neighborhood.Vorspiel

/-!
# Maximal consistent sets

Lindenbaum's lemma, extending a consistent set of formulas to a maximal one, and the maximal
consistent sets of a logic together with the behaviour of membership under the connectives.
-/

@[expose] public section

namespace LO.Modal

namespace FormulaSet

open Logic Logic.Context

variable {L : Logic} {T : FormulaSet}

/-- Every consistent set of formulas extends to a maximal one. -/
lemma exists_consistent_maximal_of_consistent (hT : Consistent L T) :
    ∃ Z, Consistent L Z ∧ T ⊆ Z ∧ ∀ U, Consistent L U → Z ⊆ U → U = Z := by
  have hchain : ∀ c ⊆ { X : FormulaSet | Consistent L X }, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ { X : FormulaSet | Consistent L X }, ∀ s ∈ c, s ⊆ ub := by
    intro c hc chain hnc;
    refine ⟨⋃₀ c, ?_, fun s hs => Set.subset_sUnion_of_mem hs⟩;
    apply def_consistent.mpr;
    intro Γ hΓ hC;
    obtain ⟨U, hUc, hUs⟩ :=
      Set.subset_mem_chain_of_finite c hnc chain (s := ↑Γ) Γ.finite_toSet hΓ;
    exact def_consistent.mp (hc hUc) Γ hUs hC;
  obtain ⟨Z, hTZ, hmax⟩ := zorn_subset_nonempty _ hchain T hT;
  refine ⟨Z, hmax.prop, hTZ, ?_⟩;
  intro U hU hZU;
  exact Set.Subset.antisymm (hmax.2 hU hZU) hZU;

protected alias lindenbaum := exists_consistent_maximal_of_consistent

end FormulaSet

open FormulaSet

/-- A maximal consistent set of formulas of the logic `L`. -/
abbrev MaximalConsistentSet (L : Logic) :=
  { T : FormulaSet // Consistent L T ∧ ∀ {U}, T ⊂ U → Inconsistent L U }

namespace MaximalConsistentSet

open Logic Logic.Context

variable {L : Logic} {Ω Ω₁ Ω₂ : MaximalConsistentSet L} {T : FormulaSet} {φ ψ : Formula}

instance : Membership Formula (MaximalConsistentSet L) := ⟨fun Ω φ => φ ∈ Ω.1⟩

lemma consistent (Ω : MaximalConsistentSet L) : Consistent L Ω.1 := Ω.2.1

lemma maximal (Ω : MaximalConsistentSet L) {U} (h : Ω.1 ⊂ U) : Inconsistent L U := Ω.2.2 h

lemma maximal' (Ω : MaximalConsistentSet L) (h : φ ∉ Ω) : Inconsistent L (insert φ Ω.1) :=
  Ω.maximal (Set.ssubset_insert h)

lemma equality_def : Ω₁ = Ω₂ ↔ Ω₁.1 = Ω₂.1 := Subtype.ext_iff

section

variable [L.Cl]

/-- Every consistent set of formulas is contained in a maximal consistent set. -/
lemma exists_of_consistent (hT : Consistent L T) : ∃ Ω : MaximalConsistentSet L, T ⊆ Ω.1 := sorry

alias lindenbaum := exists_of_consistent

instance [L.Consistent] : Nonempty (MaximalConsistentSet L) := sorry

lemma either_mem (Ω : MaximalConsistentSet L) (φ) : φ ∈ Ω ∨ ∼φ ∈ Ω := sorry

lemma membership_iff : φ ∈ Ω ↔ Ω.1 *⊢[L] φ := sorry

@[simp] lemma not_mem_falsum : ⊥ ∉ Ω := sorry

@[simp] lemma mem_verum : ⊤ ∈ Ω := sorry

@[simp] lemma iff_mem_neg : ∼φ ∈ Ω ↔ φ ∉ Ω := sorry

lemma iff_forall_mem_provable : (∀ Ω : MaximalConsistentSet L, φ ∈ Ω) ↔ φ ∈ L := sorry

@[grind ←] lemma mem_of_prove (h : φ ∈ L) : φ ∈ Ω := iff_forall_mem_provable.mpr h Ω

@[simp] lemma iff_mem_negneg : ∼∼φ ∈ Ω ↔ φ ∈ Ω := by simp

@[simp, grind =] lemma iff_mem_imp : φ 🡒 ψ ∈ Ω ↔ (φ ∈ Ω → ψ ∈ Ω) := sorry

lemma mdp (hφψ : φ 🡒 ψ ∈ Ω) (hφ : φ ∈ Ω) : ψ ∈ Ω := iff_mem_imp.mp hφψ hφ

lemma mdp_provable (hφψ : φ 🡒 ψ ∈ L) (hφ : φ ∈ Ω) : ψ ∈ Ω := mdp (mem_of_prove hφψ) hφ

@[simp] lemma iff_mem_and : φ ⋏ ψ ∈ Ω ↔ φ ∈ Ω ∧ ψ ∈ Ω := sorry

@[simp] lemma iff_mem_or : φ ⋎ ψ ∈ Ω ↔ φ ∈ Ω ∨ ψ ∈ Ω := sorry

lemma iff_congr (h : Ω.1 *⊢[L] φ 🡘 ψ) : φ ∈ Ω ↔ ψ ∈ Ω := sorry

lemma intro_equality (h : ∀ φ, φ ∈ Ω₁.1 → φ ∈ Ω₂.1) : Ω₁ = Ω₂ := sorry

lemma neg_imp (h : ψ ∈ Ω₂ → φ ∈ Ω₁) : ∼φ ∈ Ω₁ → ∼ψ ∈ Ω₂ := sorry

lemma neg_iff (h : φ ∈ Ω₁ ↔ ψ ∈ Ω₂) : ∼φ ∈ Ω₁ ↔ ∼ψ ∈ Ω₂ := ⟨neg_imp h.mpr, neg_imp h.mp⟩

end

end MaximalConsistentSet

end LO.Modal

end
