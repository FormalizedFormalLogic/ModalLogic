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

abbrev frame_3_8421506 : Frame (Fin 3) :=
  ⟨fun w => match w with
    | 0 => {{0}, Set.univ}
    | 1 => {Set.univ}
    | 2 => {Set.univ}⟩

instance : frame_3_8421506.ContainsUnit := ⟨by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_8421506]⟩

lemma frame_3_8421506.box_singleton_zero :
    frame_3_8421506.box ({0} : Set (Fin 3)) = {0} := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_8421506]

lemma frame_3_8421506.box_doubleton_zero_one :
    frame_3_8421506.box ({0, 1} : Set (Fin 3)) = ∅ := by
  ext w
  fin_cases w <;>
    simp only [Frame.box, frame_3_8421506, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false] <;>
    simp only [Set.ext_iff] <;> decide

instance : frame_3_8421506.IsSerial where
  serial X w hw := by
    simp only [Frame.dia, Frame.box, Set.mem_compl_iff, Set.mem_setOf_eq]
    fin_cases w <;>
      simp only [Frame.box, frame_3_8421506, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw ⊢ <;>
      rcases hw with rfl | rfl <;> simp only [Set.ext_iff] <;> decide

instance : frame_3_8421506.IsTransitive where
  trans X w hw := by
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    fin_cases w <;>
      simp only [Frame.box, frame_3_8421506, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw
    · rcases hw with rfl | rfl
      · simp [frame_3_8421506.box_singleton_zero]
      · simp [frame_3_8421506.contains_unit]
    · subst hw; simp [frame_3_8421506.contains_unit]
    · subst hw; simp [frame_3_8421506.contains_unit]

@[simp]
lemma frame_3_8421506.not_valid_axiomK [DecidableEq α] (hab : a ≠ b) :
    ¬frame_3_8421506 ⊧ (Axioms.K #a #b : Formula α) := fun h => by
  have h0 := h (fun c => if c = a then {0} else if c = b then {0, 1} else Set.univ) 0
  simp [Forces, Frame.box, Set.ext_iff, Ne.symm hab] at h0
  revert h0
  decide

@[simp]
lemma frame_3_8421506.not_valid_axiomM [DecidableEq α] (hab : a ≠ b) :
    ¬frame_3_8421506 ⊧ (Axioms.M #a #b : Formula α) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun c => if c = a then {0} else if c = b then {0, 1} else Set.univ, 0, by
      unfold NotForces Forces
      simp [Frame.box, frame_3_8421506, Set.ext_iff, Ne.symm hab]
      decide⟩

end
