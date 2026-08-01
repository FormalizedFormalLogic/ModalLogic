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
variable {a : α}

abbrev frame_2_95 : Frame (Fin 2) :=
  ⟨fun w => match w with | 0 => {∅, {0}} | 1 => {∅, {0}, {1}, Set.univ}⟩

lemma frame_2_95.box_empty : frame_2_95.box (∅ : Set (Fin 2)) = Set.univ := by
  ext y; fin_cases y <;> simp [Frame.box, frame_2_95]

lemma frame_2_95.box_zero : frame_2_95.box ({0} : Set (Fin 2)) = Set.univ := by
  ext y; fin_cases y <;> simp [Frame.box, frame_2_95]

lemma frame_2_95.box_one : frame_2_95.box ({1} : Set (Fin 2)) = {1} := by
  ext y; fin_cases y <;> simp [Frame.box, frame_2_95]

lemma frame_2_95.box_univ : frame_2_95.box (Set.univ : Set (Fin 2)) = {1} := by
  ext y; fin_cases y <;> simp [Frame.box, frame_2_95, Set.ext_iff]

instance : frame_2_95.IsRegular where
  regular X Y := by
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;>
      rcases Set.Fin2.all_cases Y with rfl | rfl | rfl | rfl <;>
        simp [frame_2_95.box_empty, frame_2_95.box_zero, frame_2_95.box_one]

instance : frame_2_95.IsEuclidean where
  eucl X := by
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;>
      simp [Frame.dia, ← Set.Fin2.eq_univ, frame_2_95.box_empty, frame_2_95.box_zero,
        frame_2_95.box_one, frame_2_95.box_univ]

instance : frame_2_95.IsSymmetric where
  symm X := by
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;>
      simp [Frame.dia, ← Set.Fin2.eq_univ, frame_2_95.box_empty, frame_2_95.box_zero,
        frame_2_95.box_one, frame_2_95.box_univ]

lemma frame_2_95.not_containsUnit : ¬frame_2_95.ContainsUnit := by
  intro h
  have := h.contains_unit
  rw [frame_2_95.box_univ] at this
  simp [Set.Fin2.eq_univ, Set.ext_iff] at this

lemma frame_2_95.not_valid_axiomN :
    ¬frame_2_95 ⊧ (Axioms.N : Formula α) :=
  fun h => frame_2_95.not_containsUnit (containsUnit_of_valid_axiomN h)

end
