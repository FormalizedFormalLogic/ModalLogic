module

public import Neighborhood.Semantics.AxiomM
public import Neighborhood.Semantics.AxiomC
public import Neighborhood.Semantics.AxiomN
public import Neighborhood.Semantics.AxiomP
public import Neighborhood.Semantics.AxiomK
public import Neighborhood.Semantics.AxiomGeach

@[expose] public section

variable {α : Type u}
variable {a b : α}

abbrev frame_2_153 : Frame (Fin 2) := ⟨fun _ => {∅, Set.univ}⟩

@[simp]
lemma frame_2_153.not_valid_axiomK [DecidableEq α] (hab : a ≠ b) :
    ¬frame_2_153 ⊧ (Axioms.K #a #b : Formula α) := fun h => by
  have h0 := h (fun c => if c = a then ∅ else if c = b then {0} else Set.univ) 0
  simp [Forces, Frame.box, Set.ext_iff, Ne.symm hab] at h0

@[simp]
lemma frame_2_153.not_valid_axiomM [DecidableEq α] (hab : a ≠ b) :
    ¬frame_2_153 ⊧ (Axioms.M #a #b : Formula α) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun c => if c = a then {0} else if c = b then {1} else Set.univ, 0, by
      unfold NotForces Forces
      simp [Frame.box, frame_2_153, Set.ext_iff, Ne.symm hab]⟩

instance : frame_2_153.IsRegular where
  regular X Y w hw := by
    simp only [Frame.box, frame_2_153, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw ⊢
    obtain ⟨hX, hY⟩ := hw
    rcases hX with rfl | rfl <;> rcases hY with rfl | rfl <;> simp

instance : frame_2_153.ContainsUnit := ⟨by
  ext w
  simp [Frame.box, frame_2_153]⟩

lemma frame_2_153.box_empty_eq_univ :
    frame_2_153.box (∅ : Set (Fin 2)) = Set.univ := by
  ext w; simp [Frame.box, frame_2_153]

lemma frame_2_153.box_univ_eq_univ :
    frame_2_153.box (Set.univ : Set (Fin 2)) = Set.univ := by
  ext w; simp [Frame.box, frame_2_153]

/-- Every box of `frame_2_153` is either empty or the whole frame: the neighborhoods of a world
are exactly `∅` and `univ`, so a set is a neighborhood of every world exactly when it is one of
these two boundary values. -/
lemma frame_2_153.box_eq_univ_or_empty (X : Set (Fin 2)) :
    frame_2_153.box X = ∅ ∨ frame_2_153.box X = Set.univ := by
  by_cases h : X = ∅ ∨ X = Set.univ
  · right
    rcases h with rfl | rfl
    · exact frame_2_153.box_empty_eq_univ
    · exact frame_2_153.box_univ_eq_univ
  · left; ext w; simp only [Frame.box, frame_2_153, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]; tauto

lemma frame_2_153.dia_eq_univ_or_empty (X : Set (Fin 2)) :
    frame_2_153.dia X = ∅ ∨ frame_2_153.dia X = Set.univ := by
  rcases frame_2_153.box_eq_univ_or_empty Xᶜ with h | h
  · right; simp [Frame.dia, h]
  · left; simp [Frame.dia, h]

instance : frame_2_153.IsTransitive where
  trans X := by
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    rcases frame_2_153.box_eq_univ_or_empty X with h | h <;>
      rw [h] <;> simp [frame_2_153.box_empty_eq_univ, frame_2_153.box_univ_eq_univ]

instance : frame_2_153.IsEuclidean where
  eucl X := by
    rcases frame_2_153.dia_eq_univ_or_empty X with h | h <;>
      rw [h] <;> simp [frame_2_153.box_empty_eq_univ, frame_2_153.box_univ_eq_univ]

end
