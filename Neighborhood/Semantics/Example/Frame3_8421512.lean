module

public import Neighborhood.Semantics.AxiomM
public import Neighborhood.Semantics.AxiomC
public import Neighborhood.Semantics.AxiomN
public import Neighborhood.Semantics.AxiomP
public import Neighborhood.Semantics.AxiomK
public import Neighborhood.Semantics.AxiomGeach
import Mathlib.Tactic.FinCases

@[expose] public section

variable {α : Type u}

abbrev frame_3_8421512 : Frame (Fin 3) :=
  ⟨fun w => match w with
    | 0 => {{0, 1}, Set.univ}
    | 1 => {Set.univ}
    | 2 => {Set.univ}⟩

instance : frame_3_8421512.ContainsUnit := ⟨by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_8421512]⟩

instance : frame_3_8421512.IsReflexive where
  refl X w hw := by
    fin_cases w <;>
      simp only [Frame.box, frame_3_8421512, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw ⊢ <;>
      rcases hw with rfl | rfl <;> simp

lemma frame_3_8421512.box_zero_one :
    frame_3_8421512.box ({0, 1} : Set (Fin 3)) = {0} := by
  ext w
  fin_cases w <;> simp [Frame.box, frame_3_8421512, Set.ext_iff] <;> decide

lemma frame_3_8421512.box_singleton_zero :
    frame_3_8421512.box ({0} : Set (Fin 3)) = ∅ := by
  ext w
  fin_cases w <;> simp [Frame.box, frame_3_8421512, Set.ext_iff] <;> decide

lemma frame_3_8421512.box_mono {X Y : Set (Fin 3)} (h : X ⊆ Y) :
    frame_3_8421512.box X ⊆ frame_3_8421512.box Y := by
  intro w hw
  change X ∈ frame_3_8421512.𝒩 w at hw
  change Y ∈ frame_3_8421512.𝒩 w
  fin_cases w <;>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢
  · rcases hw with rfl | rfl
    · have h0 : (0 : Fin 3) ∈ Y := h (by simp)
      have h1 : (1 : Fin 3) ∈ Y := h (by simp)
      by_cases h2 : (2 : Fin 3) ∈ Y
      · right; ext i; fin_cases i <;> simp_all
      · left; ext i; fin_cases i <;> simp_all
    · right; ext i
      have : i ∈ (Set.univ : Set (Fin 3)) := trivial
      have := h this
      fin_cases i <;> simp_all
  · rw [hw] at h
    exact Set.univ_subset_iff.mp h
  · rw [hw] at h
    exact Set.univ_subset_iff.mp h

instance : frame_3_8421512.IsMonotonic where
  mono _ _ := Set.subset_inter
    (frame_3_8421512.box_mono Set.inter_subset_left)
    (frame_3_8421512.box_mono Set.inter_subset_right)

instance : frame_3_8421512.IsRegular where
  regular X Y w hw := by
    have hw' : X ∈ frame_3_8421512.𝒩 w ∧ Y ∈ frame_3_8421512.𝒩 w := hw
    change X ∩ Y ∈ frame_3_8421512.𝒩 w
    fin_cases w <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw' ⊢
    · obtain ⟨hX, hY⟩ := hw'
      rcases hX with rfl | rfl <;> rcases hY with rfl | rfl <;> simp
    · obtain ⟨rfl, rfl⟩ := hw'; simp
    · obtain ⟨rfl, rfl⟩ := hw'; simp

lemma frame_3_8421512.not_isTransitive :
    ¬frame_3_8421512.IsTransitive := by
  intro hC
  have h := hC.trans ({0, 1} : Set (Fin 3))
    (show (0 : Fin 3) ∈ frame_3_8421512.box {0, 1} by
      rw [frame_3_8421512.box_zero_one]; rfl)
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq] at h
  rw [frame_3_8421512.box_zero_one, frame_3_8421512.box_singleton_zero] at h
  exact h

lemma frame_3_8421512.not_valid_axiomFour :
    ¬frame_3_8421512 ⊧ (Axioms.Four #0 : Formula ℕ) :=
  fun h => frame_3_8421512.not_isTransitive (isTransitive_of_valid_axiomFour h)

end
