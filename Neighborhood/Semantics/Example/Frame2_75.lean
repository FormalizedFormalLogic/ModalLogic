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

abbrev frame_2_75 : Frame (Fin 2) :=
  ⟨fun w => match w with
    | 0 => {∅, {0}, Set.univ}
    | 1 => {{1}}⟩

lemma frame_2_75.not_containsUnit : ¬frame_2_75.ContainsUnit := by
  intro h
  have h1 : (1 : Fin 2) ∈ frame_2_75.box (Set.univ : Set (Fin 2)) := by
    rw [h.contains_unit]; trivial
  simp [Frame.box, frame_2_75, Set.Fin2.eq_univ, Set.ext_iff] at h1

lemma frame_2_75.not_valid_axiomN :
    ¬frame_2_75 ⊧ (Axioms.N : Formula α) :=
  fun h => frame_2_75.not_containsUnit (containsUnit_of_valid_axiomN h)

instance : frame_2_75.IsEuclidean where
  eucl X := by
    have hbox0 : frame_2_75.box ({0} : Set (Fin 2)) = {0} := by
      ext y; fin_cases y <;> simp [Frame.box, frame_2_75, Set.Fin2.eq_univ, Set.ext_iff]
    have hbox1 : frame_2_75.box ({1} : Set (Fin 2)) = {1} := by
      ext y; fin_cases y <;> simp [Frame.box, frame_2_75, Set.Fin2.eq_univ, Set.ext_iff]
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl
    · have hdia : frame_2_75.dia ({0, 1} : Set (Fin 2)) = {1} := by
        ext y; fin_cases y <;> simp [Frame.dia, Frame.box, frame_2_75, Set.Fin2.eq_univ, Set.ext_iff]
      rw [hdia, hbox1]

    · have hdia : frame_2_75.dia ({0} : Set (Fin 2)) = {0} := by
        ext y; fin_cases y <;> simp [Frame.dia, Frame.box, frame_2_75, Set.Fin2.eq_univ, Set.ext_iff]
      rw [hdia, hbox0]
    · have hdia : frame_2_75.dia ({1} : Set (Fin 2)) = {1} := by
        ext y; fin_cases y <;> simp [Frame.dia, Frame.box, frame_2_75, Set.Fin2.eq_univ, Set.ext_iff]
      rw [hdia, hbox1]

    · have hdia : frame_2_75.dia (∅ : Set (Fin 2)) = {1} := by
        ext y; fin_cases y <;> simp [Frame.dia, Frame.box, frame_2_75, Set.Fin2.eq_univ, Set.ext_iff]
      rw [hdia, hbox1]


instance : frame_2_75.IsRegular where
  regular X Y := by
    have hbox0 : frame_2_75.box ({0} : Set (Fin 2)) = {0} := by
      ext y; fin_cases y <;> simp [Frame.box, frame_2_75, Set.Fin2.eq_univ, Set.ext_iff]
    have hbox1 : frame_2_75.box ({1} : Set (Fin 2)) = {1} := by
      ext y; fin_cases y <;> simp [Frame.box, frame_2_75, Set.Fin2.eq_univ, Set.ext_iff]
    have hboxE : frame_2_75.box (∅ : Set (Fin 2)) = {0} := by
      ext y; fin_cases y <;> simp [Frame.box, frame_2_75, Set.Fin2.eq_univ, Set.ext_iff]
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;>
      rcases Set.Fin2.all_cases Y with rfl | rfl | rfl | rfl <;>
        simp [hbox0, hbox1, hboxE]

instance : frame_2_75.IsTransitive where
  trans X := by
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    have hbox0 : frame_2_75.box ({0} : Set (Fin 2)) = {0} := by
      ext y; fin_cases y <;> simp [Frame.box, frame_2_75, Set.Fin2.eq_univ, Set.ext_iff]
    have hbox1 : frame_2_75.box ({1} : Set (Fin 2)) = {1} := by
      ext y; fin_cases y <;> simp [Frame.box, frame_2_75, Set.Fin2.eq_univ, Set.ext_iff]
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl
    · have hboxU : frame_2_75.box ({0, 1} : Set (Fin 2)) = {0} := by
        ext y; fin_cases y <;> simp [Frame.box, frame_2_75, Set.Fin2.eq_univ, Set.ext_iff]
      rw [hboxU, hbox0]
    · rw [hbox0, hbox0]
    · rw [hbox1, hbox1]
    · have hboxE : frame_2_75.box (∅ : Set (Fin 2)) = {0} := by
        ext y; fin_cases y <;> simp [Frame.box, frame_2_75, Set.Fin2.eq_univ, Set.ext_iff]
      rw [hboxE, hbox0]

end
