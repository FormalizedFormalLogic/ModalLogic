module

public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Preorder.Chain

/-!
# Auxiliary set-theoretic lemmas

Small `Set` lemmas that Mathlib does not provide, used for enumerating the powerset of a
finite frame's carrier and for the Zorn-style construction of maximal consistent sets.
-/

@[expose] public section

namespace Set

namespace Fin1

protected lemma eq_univ : Set.univ (α := Fin 1) = {0} := by ext x; match x with | 0 => simp

protected lemma eq_powerset : Set.powerset (Set.univ : Set (Fin 1)) = {{0}, ∅} := by
  ext x;
  simp only [Set.powerset_univ, Set.mem_univ, Fin.isValue, Set.mem_insert_iff,
    Set.mem_singleton_iff, true_iff];
  by_cases h : 0 ∈ x;
  . left; ext i; match i with | 0 => simp_all;
  . right; ext i; match i with | 0 => simp_all;

protected lemma all_cases (s : Set (Fin 1)) : s = {0} ∨ s = ∅ := by
  simpa using Set.Fin1.eq_powerset.subset (by simp);

end Fin1

namespace Fin2

protected lemma eq_univ : Set.univ (α := Fin 2) = {0, 1} := by ext x; match x with | 0 | 1 => simp

@[simp]
protected lemma ne_singleton_univ {x : Fin 2} : ({x} : Set (Fin 2)) ≠ Set.univ := by
  apply Set.Subset.antisymm_iff.not.mpr;
  suffices 0 = x → ¬1 = x by simpa;
  grind;

protected lemma eq_powerset :
    Set.powerset (Set.univ : Set (Fin 2)) = {{0, 1}, {0}, {1}, ∅} := by
  ext x;
  simp only [Set.powerset_univ, Set.mem_univ, Fin.isValue, Set.mem_insert_iff,
    Set.mem_singleton_iff, true_iff];
  by_cases h0 : 0 ∈ x <;>
  by_cases h1 : 1 ∈ x;
  . left;
    ext i;
    match i with | 0 | 1 => simp_all;
  . right; left;
    ext i;
    match i with | 0 | 1 => simp_all;
  . right; right; left;
    ext i;
    match i with | 0 | 1 => simp_all;
  . right; right; right;
    ext i;
    match i with | 0 | 1 => simp_all;

protected lemma all_cases (s : Set (Fin 2)) : s = {0, 1} ∨ s = {0} ∨ s = {1} ∨ s = ∅ := by
  simpa using Set.Fin2.eq_powerset.subset (by simp);

@[simp]
lemma eq_compl_singleton_one_singleton_zero : ({1}ᶜ : Set (Fin 2)) = {0} := by
  apply Set.Subset.antisymm_iff.mpr;
  constructor;
  . intro;
    simp;
    omega;
  . simp;

@[simp]
lemma eq_compl_singleton_zero_singleton_one : ({0}ᶜ : Set (Fin 2)) = {1} := by
  apply Set.Subset.antisymm_iff.mpr;
  constructor;
  . intro;
    simp;
    omega;
  . simp;

end Fin2

/-- Every finite subset of the union of a nonempty chain is contained in one of its members. -/
lemma subset_mem_chain_of_finite (c : Set (Set α)) (hc : Set.Nonempty c)
    (hchain : IsChain (· ⊆ ·) c) {s} (hfin : Set.Finite s) : s ⊆ ⋃₀ c → ∃ t ∈ c, s ⊆ t :=
  Set.Finite.induction_on s hfin
    (by obtain ⟨t, ht⟩ := hc; intro; exact ⟨t, ht, by simp⟩)
    (by intro a s _ _ ih h;
        obtain ⟨t, htc, ht⟩ : ∃ t ∈ c, s ⊆ t := ih (subset_trans (Set.subset_insert a s) h);
        obtain ⟨u, huc, hu⟩ : ∃ u ∈ c, a ∈ u := by
          have : (∃ t ∈ c, a ∈ t) ∧ s ⊆ ⋃₀ c := by simpa [Set.insert_subset_iff] using h;
          exact this.1;
        obtain ⟨z, hzc, htz, huz⟩ : ∃ z ∈ c, t ⊆ z ∧ u ⊆ z := hchain.directedOn t htc u huc;
        exact ⟨z, hzc, Set.insert_subset (huz hu) (Set.Subset.trans ht htz)⟩)

end Set

@[simp]
lemma Set.inter_eq_univ {s t : Set α} : s ∩ t = Set.univ ↔ s = Set.univ ∧ t = Set.univ := by
  simpa using Set.sInter_eq_univ (S := ({s, t} : Set (Set α)))

end
