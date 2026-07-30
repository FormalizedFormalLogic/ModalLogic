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

abbrev frame_2_90 : Frame (Fin 2) :=
  ⟨fun w => match w with
    | 0 => {{0}, Set.univ}
    | 1 => {∅, {1}}⟩

lemma frame_2_90.not_containsUnit : ¬frame_2_90.ContainsUnit := by
  intro h
  have h1 : (1 : Fin 2) ∈ frame_2_90.box (Set.univ : Set (Fin 2)) := by
    rw [h.contains_unit]; trivial
  simp [Frame.box, frame_2_90, Set.Fin2.eq_univ, Set.ext_iff] at h1

lemma frame_2_90.not_valid_axiomN :
    ¬frame_2_90 ⊧ (Axioms.N : Formula ℕ) :=
  fun h => frame_2_90.not_containsUnit (containsUnit_of_valid_axiomN h)

instance : frame_2_90.IsEuclidean where
  eucl X := by
    have hbox0 : frame_2_90.box ({0} : Set (Fin 2)) = {0} := by
      ext y; fin_cases y <;> simp [Frame.box, frame_2_90, Set.Fin2.eq_univ, Set.ext_iff]
    have hbox1 : frame_2_90.box ({1} : Set (Fin 2)) = {1} := by
      ext y; fin_cases y <;> simp [Frame.box, frame_2_90, Set.Fin2.eq_univ, Set.ext_iff]
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl
    · have hdia : frame_2_90.dia ({0, 1} : Set (Fin 2)) = {0} := by
        ext y; fin_cases y <;> simp [Frame.dia, Frame.box, frame_2_90, Set.Fin2.eq_univ, Set.ext_iff]
      rw [hdia, hbox0]
    · have hdia : frame_2_90.dia ({0} : Set (Fin 2)) = {0} := by
        ext y; fin_cases y <;> simp [Frame.dia, Frame.box, frame_2_90, Set.Fin2.eq_univ, Set.ext_iff]
      rw [hdia, hbox0]
    · have hdia : frame_2_90.dia ({1} : Set (Fin 2)) = {1} := by
        ext y; fin_cases y <;> simp [Frame.dia, Frame.box, frame_2_90, Set.Fin2.eq_univ, Set.ext_iff]
      rw [hdia, hbox1]
    · have hdia : frame_2_90.dia (∅ : Set (Fin 2)) = {1} := by
        ext y; fin_cases y <;> simp [Frame.dia, Frame.box, frame_2_90, Set.Fin2.eq_univ, Set.ext_iff]
      rw [hdia, hbox1]

instance : frame_2_90.IsSerial where
  serial X := by
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;>
      intro y hy <;> fin_cases y <;>
        simp_all [Frame.box, Frame.dia, frame_2_90, Set.Fin2.eq_univ, Set.ext_iff]

end
