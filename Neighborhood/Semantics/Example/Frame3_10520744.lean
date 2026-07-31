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
variable {a b : α}

abbrev frame_3_10520744 : Frame (Fin 3) :=
  ⟨fun w => match w with
    | 0 => {{0, 1}, {0, 2}, Set.univ}
    | 1 => {{0, 1}, Set.univ}
    | 2 => {{0, 2}, Set.univ}⟩

instance : frame_3_10520744.ContainsUnit := ⟨by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_10520744]⟩

instance : frame_3_10520744.IsReflexive where
  refl X w hw := by
    fin_cases w <;>
      simp only [Frame.box, frame_3_10520744, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw ⊢ <;>
      rcases hw with rfl | rfl | rfl <;> simp

lemma frame_3_10520744.box_zero_one :
    frame_3_10520744.box ({0, 1} : Set (Fin 3)) = {0, 1} := by
  ext w
  fin_cases w <;> simp [Frame.box, frame_3_10520744, Set.ext_iff]; decide

lemma frame_3_10520744.box_zero_two :
    frame_3_10520744.box ({0, 2} : Set (Fin 3)) = {0, 2} := by
  ext w
  fin_cases w <;> simp [Frame.box, frame_3_10520744, Set.ext_iff]; decide

lemma frame_3_10520744.box_univ :
    frame_3_10520744.box (Set.univ : Set (Fin 3)) = Set.univ := by
  ext w
  fin_cases w <;> simp [Frame.box, frame_3_10520744]

instance : frame_3_10520744.IsTransitive where
  trans X w hw := by
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    have hw' : X ∈ frame_3_10520744.𝒩 w := hw
    change frame_3_10520744.box X ∈ frame_3_10520744.𝒩 w
    fin_cases w <;>
      simp only [frame_3_10520744, Set.mem_insert_iff, Set.mem_singleton_iff] at hw' ⊢
    · rcases hw' with rfl | rfl | rfl <;>
        simp [frame_3_10520744.box_zero_one, frame_3_10520744.box_zero_two,
          frame_3_10520744.box_univ]
    · rcases hw' with rfl | rfl <;>
        simp [frame_3_10520744.box_zero_one, frame_3_10520744.box_univ]
    · rcases hw' with rfl | rfl <;>
        simp [frame_3_10520744.box_zero_two, frame_3_10520744.box_univ]

lemma frame_3_10520744.box_mono {X Y : Set (Fin 3)} (h : X ⊆ Y) :
    frame_3_10520744.box X ⊆ frame_3_10520744.box Y := by
  intro w hw
  fin_cases w
  · simp only [Frame.box, frame_3_10520744, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw ⊢
    rcases hw with rfl | rfl | rfl
    · have h0 : (0 : Fin 3) ∈ Y := h (by simp)
      have h1 : (1 : Fin 3) ∈ Y := h (by simp)
      by_cases h2 : (2 : Fin 3) ∈ Y
      · right; right; ext i; fin_cases i <;> simp_all
      · left; ext i; fin_cases i <;> simp_all
    · have h0 : (0 : Fin 3) ∈ Y := h (by simp)
      have h2 : (2 : Fin 3) ∈ Y := h (by simp)
      by_cases h1 : (1 : Fin 3) ∈ Y
      · right; right; ext i; fin_cases i <;> simp_all
      · right; left; ext i; fin_cases i <;> simp_all
    · right; right; ext i
      have : i ∈ Set.univ := trivial
      have := h this
      fin_cases i <;> simp_all
  · simp only [Frame.box, frame_3_10520744, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw ⊢
    rcases hw with rfl | rfl
    · have h0 : (0 : Fin 3) ∈ Y := h (by simp)
      have h1 : (1 : Fin 3) ∈ Y := h (by simp)
      by_cases h2 : (2 : Fin 3) ∈ Y
      · right; ext i; fin_cases i <;> simp_all
      · left; ext i; fin_cases i <;> simp_all
    · right; ext i
      have : i ∈ Set.univ := trivial
      have := h this
      fin_cases i <;> simp_all
  · simp only [Frame.box, frame_3_10520744, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw ⊢
    rcases hw with rfl | rfl
    · have h0 : (0 : Fin 3) ∈ Y := h (by simp)
      have h2 : (2 : Fin 3) ∈ Y := h (by simp)
      by_cases h1 : (1 : Fin 3) ∈ Y
      · right; ext i; fin_cases i <;> simp_all
      · left; ext i; fin_cases i <;> simp_all
    · right; ext i
      have : i ∈ Set.univ := trivial
      have := h this
      fin_cases i <;> simp_all

instance : frame_3_10520744.IsMonotonic where
  mono _ _ := Set.subset_inter
    (frame_3_10520744.box_mono Set.inter_subset_left)
    (frame_3_10520744.box_mono Set.inter_subset_right)

lemma frame_3_10520744.not_isRegular :
    ¬frame_3_10520744.IsRegular := fun hR => by
  have h := hR.regular ({0, 1} : Set (Fin 3)) ({0, 2} : Set (Fin 3))
  rw [frame_3_10520744.box_zero_one, frame_3_10520744.box_zero_two] at h
  have heq : ({0, 1} : Set (Fin 3)) ∩ {0, 2} = ({0} : Set (Fin 3)) := by
    ext i; fin_cases i <;> simp
  have h0 : (0 : Fin 3) ∈ frame_3_10520744.box ({0} : Set (Fin 3)) := by
    rw [← heq]
    exact h (show (0 : Fin 3) ∈ ({0, 1} : Set (Fin 3)) ∩ {0, 2} by simp)
  change ({0} : Set (Fin 3)) ∈ frame_3_10520744.𝒩 0 at h0
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h0
  rcases h0 with h0 | h0 | h0
  · exact absurd ((Set.ext_iff.mp h0 1).mpr (by simp)) (by simp)
  · exact absurd ((Set.ext_iff.mp h0 2).mpr (by simp)) (by simp)
  · exact absurd ((Set.ext_iff.mp h0 1).mpr (by simp)) (by simp)

@[simp]
lemma frame_3_10520744.not_valid_axiomC [DecidableEq α] (hab : a ≠ b) :
    ¬frame_3_10520744 ⊧ (Axioms.C #a #b : Formula α) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun c => if c = a then {0, 1} else if c = b then {0, 2} else Set.univ, 0, by
      unfold NotForces Forces
      simp [Frame.box, frame_3_10520744, Set.ext_iff, Ne.symm hab]
      decide⟩

end
