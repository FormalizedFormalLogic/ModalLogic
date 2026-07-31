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

abbrev frame_3_8421544 : Frame (Fin 3) :=
  ⟨fun w => match w with
    | 0 => {{0, 1}, {0, 2}, Set.univ}
    | 1 => {Set.univ}
    | 2 => {Set.univ}⟩

instance : frame_3_8421544.ContainsUnit := ⟨by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_8421544]⟩

private lemma frame_3_8421544.superset_zero_one {Y : Set (Fin 3)}
    (h : ({0, 1} : Set (Fin 3)) ⊆ Y) : Y = {0, 1} ∨ Y = Set.univ := by
  have h0 : (0 : Fin 3) ∈ Y := h (by simp)
  have h1 : (1 : Fin 3) ∈ Y := h (by simp)
  by_cases h2 : (2 : Fin 3) ∈ Y
  · right; ext x; fin_cases x <;> simp [h0, h1, h2]
  · left; ext x; fin_cases x <;> simp [h0, h1, h2]

private lemma frame_3_8421544.superset_zero_two {Y : Set (Fin 3)}
    (h : ({0, 2} : Set (Fin 3)) ⊆ Y) : Y = {0, 2} ∨ Y = Set.univ := by
  have h0 : (0 : Fin 3) ∈ Y := h (by simp)
  have h2 : (2 : Fin 3) ∈ Y := h (by simp)
  by_cases h1 : (1 : Fin 3) ∈ Y
  · right; ext x; fin_cases x <;> simp [h0, h1, h2]
  · left; ext x; fin_cases x <;> simp [h0, h1, h2]

lemma frame_3_8421544.box_mono {X Y : Set (Fin 3)} (h : X ⊆ Y) :
    frame_3_8421544.box X ⊆ frame_3_8421544.box Y := by
  intro w hw
  fin_cases w <;>
    simp only [Frame.box, frame_3_8421544, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw ⊢
  · rcases hw with rfl | rfl | rfl
    · rcases frame_3_8421544.superset_zero_one h with rfl | rfl <;> simp
    · rcases frame_3_8421544.superset_zero_two h with rfl | rfl <;> simp
    · exact Or.inr (Or.inr (Set.Subset.antisymm (Set.subset_univ Y) h))
  · subst hw; exact Set.Subset.antisymm (Set.subset_univ Y) h
  · subst hw; exact Set.Subset.antisymm (Set.subset_univ Y) h

instance : frame_3_8421544.IsMonotonic where
  mono _ _ := Set.subset_inter
    (frame_3_8421544.box_mono Set.inter_subset_left)
    (frame_3_8421544.box_mono Set.inter_subset_right)

instance : frame_3_8421544.IsReflexive where
  refl X w hw := by
    fin_cases w <;>
      simp only [Frame.box, frame_3_8421544, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw <;>
      rcases hw with rfl | rfl | rfl <;> simp

lemma frame_3_8421544.box_0_1 :
    frame_3_8421544.box ({0, 1} : Set (Fin 3)) = {0} := by
  ext w
  fin_cases w <;>
    simp only [Frame.box, frame_3_8421544, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff] <;>
    simp only [Set.ext_iff] <;> decide

lemma frame_3_8421544.box_0_2 :
    frame_3_8421544.box ({0, 2} : Set (Fin 3)) = {0} := by
  ext w
  fin_cases w <;>
    simp only [Frame.box, frame_3_8421544, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff] <;>
    simp only [Set.ext_iff] <;> decide

@[simp]
lemma frame_3_8421544.not_valid_axiomC [DecidableEq α] (hab : a ≠ b) :
    ¬frame_3_8421544 ⊧ (Axioms.C #a #b : Formula α) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun c => if c = a then {0, 1} else if c = b then {0, 2} else Set.univ, 0, by
      unfold NotForces Forces
      simp [Frame.box, frame_3_8421544, Set.ext_iff, Ne.symm hab]
      decide⟩

end
