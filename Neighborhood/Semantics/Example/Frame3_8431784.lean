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

abbrev frame_3_8431784 : Frame (Fin 3) :=
  ⟨fun w => match w with
    | 0 => {{0, 1}, {0, 2}, Set.univ}
    | 1 => {{0, 1}, {0, 2}, Set.univ}
    | 2 => {Set.univ}⟩

instance : frame_3_8431784.ContainsUnit := ⟨by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_8431784]⟩

lemma frame_3_8431784.box_0_1 :
    frame_3_8431784.box ({0, 1} : Set (Fin 3)) = {0, 1} := by
  ext w
  fin_cases w <;>
    simp only [Frame.box, frame_3_8431784, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff] <;>
    simp only [Set.ext_iff] <;> decide

lemma frame_3_8431784.box_0_2 :
    frame_3_8431784.box ({0, 2} : Set (Fin 3)) = {0, 1} := by
  ext w
  fin_cases w <;>
    simp only [Frame.box, frame_3_8431784, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff] <;>
    simp only [Set.ext_iff] <;> decide

instance : frame_3_8431784.IsSerial where
  serial X w hw := by
    simp only [Frame.dia, Frame.box, Set.mem_compl_iff, Set.mem_setOf_eq]
    fin_cases w <;>
      simp only [Frame.box, frame_3_8431784, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw ⊢ <;>
      rcases hw with rfl | rfl | rfl <;> simp only [Set.ext_iff] <;> decide

instance : frame_3_8431784.IsTransitive where
  trans X w hw := by
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    fin_cases w <;>
      simp only [Frame.box, frame_3_8431784, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw
    · rcases hw with rfl | rfl | rfl
      · simp [frame_3_8431784.box_0_1]
      · simp [frame_3_8431784.box_0_2, frame_3_8431784.box_0_1]
      · simp [frame_3_8431784.contains_unit]
    · rcases hw with rfl | rfl | rfl
      · simp [frame_3_8431784.box_0_1]
      · simp [frame_3_8431784.box_0_2, frame_3_8431784.box_0_1]
      · simp [frame_3_8431784.contains_unit]
    · subst hw; simp [frame_3_8431784.contains_unit]

@[simp]
lemma frame_3_8431784.not_valid_axiomC :
    ¬frame_3_8431784 ⊧ (Axioms.C #0 #1 : Formula ℕ) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun a => match a with | 0 => {0, 1} | 1 => {0, 2} | _ => Set.univ, 0, by
      unfold NotForces Forces
      simp [Frame.box, frame_3_8431784, Set.ext_iff]
      decide⟩

end
