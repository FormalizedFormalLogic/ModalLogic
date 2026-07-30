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

omit [L.Cl] in
/-- Every consistent set of formulas is contained in a maximal consistent set. -/
lemma exists_of_consistent (hT : Consistent L T) : ∃ Ω : MaximalConsistentSet L, T ⊆ Ω.1 := by
  obtain ⟨Z, hZ, hTZ, hmax⟩ := FormulaSet.lindenbaum hT;
  refine ⟨⟨Z, hZ, ?_⟩, hTZ⟩;
  rintro U ⟨hU₁, hU₂⟩ hC;
  have := hmax U hC hU₁;
  subst this;
  simp_all;

alias lindenbaum := exists_of_consistent

instance [L.Consistent] : Nonempty (MaximalConsistentSet L) :=
  ⟨lindenbaum (T := ∅) emptyset_consistent |>.choose⟩

lemma either_mem (Ω : MaximalConsistentSet L) (φ) : φ ∈ Ω ∨ ∼φ ∈ Ω := by
  by_contra hC;
  push Not at hC;
  rcases either_consistent Ω.consistent φ with h | h;
  . exact Ω.maximal' hC.1 h;
  . exact Ω.maximal' hC.2 h;

lemma membership_iff : φ ∈ Ω ↔ Ω.1 *⊢[L] φ := by
  constructor;
  . exact by_axm!;
  . intro h;
    suffices ∼φ ∉ Ω.1 by exact or_iff_not_imp_right.mp (Ω.either_mem φ) this;
    intro hC;
    exact Ω.consistent <| mdp! (by_axm! hC) h;

@[simp] lemma not_mem_falsum : ⊥ ∉ Ω := not_mem_falsum_of_consistent Ω.consistent

@[simp] lemma mem_verum : ⊤ ∈ Ω := membership_iff.mpr <| of! verum!

@[simp] lemma iff_mem_neg : ∼φ ∈ Ω ↔ φ ∉ Ω := by
  constructor;
  . intro hn hφ;
    exact Ω.consistent <| mdp! (membership_iff.mp hn) (membership_iff.mp hφ);
  . intro hφ;
    have h : Consistent L (insert (∼φ) Ω.1) :=
      unprovable_iff_insert_neg_consistent.mpr <| membership_iff.not.mp hφ;
    have : ¬(Ω.1 ⊂ insert (∼φ) Ω.1) := fun hC => Ω.maximal hC h;
    have : insert (∼φ) Ω.1 ⊆ Ω.1 := by simpa [Set.ssubset_def] using this;
    exact this (Set.mem_insert _ _);

lemma iff_forall_mem_provable : (∀ Ω : MaximalConsistentSet L, φ ∈ Ω) ↔ φ ∈ L := by
  constructor;
  . contrapose!;
    intro h;
    obtain ⟨Ω, hΩ⟩ := lindenbaum <| unprovable_iff_singleton_neg_consistent.mpr h;
    exact ⟨Ω, iff_mem_neg.mp <| hΩ rfl⟩;
  . intro h Ω;
    exact membership_iff.mpr <| of! h;

@[grind ←] lemma mem_of_prove (h : φ ∈ L) : φ ∈ Ω := iff_forall_mem_provable.mpr h Ω

@[simp] lemma iff_mem_negneg : ∼∼φ ∈ Ω ↔ φ ∈ Ω := by simp

@[simp, grind =] lemma iff_mem_imp : φ 🡒 ψ ∈ Ω ↔ (φ ∈ Ω → ψ ∈ Ω) := by
  constructor;
  . intro hφψ hφ;
    exact membership_iff.mpr <| mdp! (membership_iff.mp hφψ) (membership_iff.mp hφ);
  . intro h;
    rcases or_iff_not_imp_left.mpr (fun hn => h (not_not.mp hn)) with hφ | hψ;
    . exact membership_iff.mpr <| of_C! CNC! <| membership_iff.mp <| iff_mem_neg.mpr hφ;
    . exact membership_iff.mpr <| of_C! implyK! <| membership_iff.mp hψ;

lemma mdp (hφψ : φ 🡒 ψ ∈ Ω) (hφ : φ ∈ Ω) : ψ ∈ Ω := iff_mem_imp.mp hφψ hφ

lemma mdp_provable (hφψ : φ 🡒 ψ ∈ L) (hφ : φ ∈ Ω) : ψ ∈ Ω := mdp (mem_of_prove hφψ) hφ

@[simp] lemma iff_mem_and : φ ⋏ ψ ∈ Ω ↔ φ ∈ Ω ∧ ψ ∈ Ω := by
  simp only [membership_iff];
  constructor;
  . intro h;
    exact ⟨of_C! and₁! h, of_C! and₂! h⟩;
  . rintro ⟨h₁, h₂⟩;
    exact of_C!_of_C! and₃! h₁ h₂;

@[simp] lemma iff_mem_or : φ ⋎ ψ ∈ Ω ↔ φ ∈ Ω ∨ ψ ∈ Ω := by
  constructor;
  . intro h;
    by_contra hC;
    push Not at hC;
    replace h := membership_iff.mp h;
    have h₁ := membership_iff.mp <| iff_mem_neg.mpr hC.1;
    have h₂ := membership_iff.mp <| iff_mem_neg.mpr hC.2;
    exact Ω.consistent <| mdp! (of_C!_of_C! or₃! h₁ h₂) h;
  . rintro (h | h);
    . exact membership_iff.mpr <| of_C! or₁! <| membership_iff.mp h;
    . exact membership_iff.mpr <| of_C! or₂! <| membership_iff.mp h;

lemma iff_congr (h : Ω.1 *⊢[L] φ 🡘 ψ) : φ ∈ Ω ↔ ψ ∈ Ω := by
  simp only [membership_iff];
  exact ⟨mdp! (of_C! and₁! h), mdp! (of_C! and₂! h)⟩;

lemma intro_equality (h : ∀ φ, φ ∈ Ω₁.1 → φ ∈ Ω₂.1) : Ω₁ = Ω₂ := by
  apply equality_def.mpr;
  apply Set.eq_of_subset_of_subset (fun φ hφ => h φ hφ);
  intro φ;
  contrapose;
  intro hφ;
  exact iff_mem_neg.mp <| h _ <| iff_mem_neg.mpr hφ;

lemma neg_imp (h : ψ ∈ Ω₂ → φ ∈ Ω₁) : ∼φ ∈ Ω₁ → ∼ψ ∈ Ω₂ := by
  contrapose;
  intro hnψ hnφ;
  have : φ ∈ Ω₁ := h <| iff_mem_negneg.mp <| iff_mem_neg.mpr hnψ;
  simpa using mdp hnφ this;

lemma neg_iff (h : φ ∈ Ω₁ ↔ ψ ∈ Ω₂) : ∼φ ∈ Ω₁ ↔ ∼ψ ∈ Ω₂ := ⟨neg_imp h.mpr, neg_imp h.mp⟩

end

end MaximalConsistentSet

end LO.Modal

end
