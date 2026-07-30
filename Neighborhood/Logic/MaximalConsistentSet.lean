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

variable {α : Type u}

namespace FormulaSet

open Logic Logic.Context

variable {L : Logic α} {T : FormulaSet α}

/-- Every consistent set of formulas extends to a maximal one. -/
lemma exists_consistent_maximal_of_consistent (hT : Consistent L T) :
    ∃ Z, Consistent L Z ∧ T ⊆ Z ∧ ∀ U, Consistent L U → Z ⊆ U → U = Z := by
  have hchain : ∀ c ⊆ { X : FormulaSet α | Consistent L X }, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ { X : FormulaSet α | Consistent L X }, ∀ s ∈ c, s ⊆ ub := by
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
abbrev MaximalConsistentSet (L : Logic α) :=
  { T : FormulaSet α // Consistent L T ∧ ∀ {U}, T ⊂ U → Inconsistent L U }

namespace MaximalConsistentSet

open Logic Logic.Context

variable {L : Logic α} {Ω Ω₁ Ω₂ : MaximalConsistentSet L} {T : FormulaSet α} {A B : Formula α}

instance : Membership (Formula α) (MaximalConsistentSet L) := ⟨fun Ω A => A ∈ Ω.1⟩

lemma consistent (Ω : MaximalConsistentSet L) : Consistent L Ω.1 := Ω.2.1

lemma maximal (Ω : MaximalConsistentSet L) {U} (h : Ω.1 ⊂ U) : Inconsistent L U := Ω.2.2 h

lemma maximal' (Ω : MaximalConsistentSet L) (h : A ∉ Ω) : Inconsistent L (insert A Ω.1) :=
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

variable [DecidableEq α]

lemma either_mem (Ω : MaximalConsistentSet L) (A) : A ∈ Ω ∨ ∼A ∈ Ω := by
  by_contra hC;
  push Not at hC;
  rcases either_consistent Ω.consistent A with h | h;
  . exact Ω.maximal' hC.1 h;
  . exact Ω.maximal' hC.2 h;

lemma membership_iff : A ∈ Ω ↔ Ω.1 *⊢[L] A := by
  constructor;
  . exact by_axm!;
  . intro h;
    suffices ∼A ∉ Ω.1 by exact or_iff_not_imp_right.mp (Ω.either_mem A) this;
    intro hC;
    exact Ω.consistent <| mdp! (by_axm! hC) h;

omit [DecidableEq α] in
@[simp] lemma not_mem_falsum : ⊥ ∉ Ω := not_mem_falsum_of_consistent Ω.consistent

@[simp] lemma mem_verum : ⊤ ∈ Ω := membership_iff.mpr <| of! verum!

@[simp] lemma iff_mem_neg : ∼A ∈ Ω ↔ A ∉ Ω := by
  constructor;
  . intro hn hA;
    exact Ω.consistent <| mdp! (membership_iff.mp hn) (membership_iff.mp hA);
  . intro hA;
    have h : Consistent L (insert (∼A) Ω.1) :=
      unprovable_iff_insert_neg_consistent.mpr <| membership_iff.not.mp hA;
    have : ¬(Ω.1 ⊂ insert (∼A) Ω.1) := fun hC => Ω.maximal hC h;
    have : insert (∼A) Ω.1 ⊆ Ω.1 := by simpa [Set.ssubset_def] using this;
    exact this (Set.mem_insert _ _);

lemma iff_forall_mem_provable : (∀ Ω : MaximalConsistentSet L, A ∈ Ω) ↔ A ∈ L := by
  constructor;
  . contrapose!;
    intro h;
    obtain ⟨Ω, hΩ⟩ := lindenbaum <| unprovable_iff_singleton_neg_consistent.mpr h;
    exact ⟨Ω, iff_mem_neg.mp <| hΩ rfl⟩;
  . intro h Ω;
    exact membership_iff.mpr <| of! h;

@[grind ←] lemma mem_of_prove (h : A ∈ L) : A ∈ Ω := iff_forall_mem_provable.mpr h Ω

@[simp] lemma iff_mem_negneg : ∼∼A ∈ Ω ↔ A ∈ Ω := by simp

@[simp, grind =] lemma iff_mem_imp : A 🡒 B ∈ Ω ↔ (A ∈ Ω → B ∈ Ω) := by
  constructor;
  . intro hAB hA;
    exact membership_iff.mpr <| mdp! (membership_iff.mp hAB) (membership_iff.mp hA);
  . intro h;
    rcases or_iff_not_imp_left.mpr (fun hn => h (not_not.mp hn)) with hA | hB;
    . exact membership_iff.mpr <| of_C! CNC! <| membership_iff.mp <| iff_mem_neg.mpr hA;
    . exact membership_iff.mpr <| of_C! implyK! <| membership_iff.mp hB;

lemma mdp (hAB : A 🡒 B ∈ Ω) (hA : A ∈ Ω) : B ∈ Ω := iff_mem_imp.mp hAB hA

lemma mdp_provable (hAB : A 🡒 B ∈ L) (hA : A ∈ Ω) : B ∈ Ω := mdp (mem_of_prove hAB) hA

@[simp] lemma iff_mem_and : A ⋏ B ∈ Ω ↔ A ∈ Ω ∧ B ∈ Ω := by
  simp only [membership_iff];
  constructor;
  . intro h;
    exact ⟨of_C! and₁! h, of_C! and₂! h⟩;
  . rintro ⟨h₁, h₂⟩;
    exact of_C!_of_C! and₃! h₁ h₂;

@[simp] lemma iff_mem_or : A ⋎ B ∈ Ω ↔ A ∈ Ω ∨ B ∈ Ω := by
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

lemma iff_congr (h : Ω.1 *⊢[L] A 🡘 B) : A ∈ Ω ↔ B ∈ Ω := by
  simp only [membership_iff];
  exact ⟨mdp! (of_C! and₁! h), mdp! (of_C! and₂! h)⟩;

lemma intro_equality (h : ∀ A, A ∈ Ω₁.1 → A ∈ Ω₂.1) : Ω₁ = Ω₂ := by
  apply equality_def.mpr;
  apply Set.eq_of_subset_of_subset (fun A hA => h A hA);
  intro A;
  contrapose;
  intro hA;
  exact iff_mem_neg.mp <| h _ <| iff_mem_neg.mpr hA;

lemma neg_imp (h : B ∈ Ω₂ → A ∈ Ω₁) : ∼A ∈ Ω₁ → ∼B ∈ Ω₂ := by
  contrapose;
  intro hnB hnA;
  have : A ∈ Ω₁ := h <| iff_mem_negneg.mp <| iff_mem_neg.mpr hnB;
  simpa using mdp hnA this;

lemma neg_iff (h : A ∈ Ω₁ ↔ B ∈ Ω₂) : ∼A ∈ Ω₁ ↔ ∼B ∈ Ω₂ := ⟨neg_imp h.mpr, neg_imp h.mp⟩

end

end MaximalConsistentSet

end
