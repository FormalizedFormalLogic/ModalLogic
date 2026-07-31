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

abbrev frame_2_186 : Frame (Fin 2) :=
  ⟨fun w => match w with
    | 0 => {{0}, Set.univ}
    | 1 => {∅, {0}, Set.univ}⟩

instance : frame_2_186.ContainsUnit := ⟨by
  ext y; fin_cases y <;> simp [Frame.box, frame_2_186, Set.Fin2.eq_univ, Set.ext_iff]⟩

instance : frame_2_186.IsEuclidean where
  eucl X := by
    have hbox0 : frame_2_186.box ({0} : Set (Fin 2)) = {0, 1} := by
      ext y; fin_cases y <;> simp [Frame.box, frame_2_186, Set.Fin2.eq_univ, Set.ext_iff]
    have hboxU : frame_2_186.box ({0, 1} : Set (Fin 2)) = {0, 1} := by
      ext y; fin_cases y <;> simp [Frame.box, frame_2_186, Set.Fin2.eq_univ, Set.ext_iff]
    have hboxE : frame_2_186.box (∅ : Set (Fin 2)) = {1} := by
      ext y; fin_cases y <;> simp [Frame.box, frame_2_186, Set.Fin2.eq_univ, Set.ext_iff]
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl
    · have hdia : frame_2_186.dia ({0, 1} : Set (Fin 2)) = {0} := by
        ext y; fin_cases y <;>
          simp [Frame.dia, Frame.box, frame_2_186, Set.Fin2.eq_univ, Set.ext_iff]
      rw [hdia, hbox0]
      exact Set.singleton_subset_iff.mpr (Set.mem_insert _ _)
    · have hdia : frame_2_186.dia ({0} : Set (Fin 2)) = {0, 1} := by
        ext y; fin_cases y <;>
          simp [Frame.dia, Frame.box, frame_2_186, Set.Fin2.eq_univ, Set.ext_iff]
      rw [hdia, hboxU]
    · have hdia : frame_2_186.dia ({1} : Set (Fin 2)) = ∅ := by
        ext y; fin_cases y <;>
          simp [Frame.dia, Frame.box, frame_2_186, Set.Fin2.eq_univ, Set.ext_iff]
      rw [hdia, hboxE]
      exact Set.empty_subset _
    · have hdia : frame_2_186.dia (∅ : Set (Fin 2)) = ∅ := by
        ext y; fin_cases y <;>
          simp [Frame.dia, Frame.box, frame_2_186, Set.Fin2.eq_univ, Set.ext_iff]
      rw [hdia, hboxE]
      exact Set.empty_subset _

instance : frame_2_186.IsRegular where
  regular X Y := by
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;>
      rcases Set.Fin2.all_cases Y with rfl | rfl | rfl | rfl <;>
        intro y hy <;> fin_cases y <;>
          simp_all [Frame.box, frame_2_186, Set.Fin2.eq_univ, Set.ext_iff]

lemma frame_2_186.not_isTransitive : ¬frame_2_186.IsTransitive := by
  intro hT
  have hboxE : frame_2_186.box (∅ : Set (Fin 2)) = {1} := by
    ext y; fin_cases y <;> simp [Frame.box, frame_2_186, Set.Fin2.eq_univ, Set.ext_iff]
  have hbox1 : frame_2_186.box ({1} : Set (Fin 2)) = ∅ := by
    ext y; fin_cases y <;> simp [Frame.box, frame_2_186, Set.Fin2.eq_univ, Set.ext_iff]
  have hiter : frame_2_186.box^[2] (∅ : Set (Fin 2)) = ∅ := by
    show frame_2_186.box (frame_2_186.box ∅) = ∅
    rw [hboxE, hbox1]
  have h1 : (1 : Fin 2) ∈ frame_2_186.box (∅ : Set (Fin 2)) := by
    rw [hboxE]; rfl
  have h2 := hT.trans (∅ : Set (Fin 2)) h1
  rw [hiter] at h2
  simp at h2

lemma frame_2_186.not_valid_axiomFour :
    ¬frame_2_186 ⊧ (Axioms.Four #a : Formula α) :=
  fun h => frame_2_186.not_isTransitive (isTransitive_of_valid_axiomFour h)

end
