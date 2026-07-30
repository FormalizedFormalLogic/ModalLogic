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

abbrev frame_2_138 : Frame (Fin 2) :=
  ⟨fun w => match w with
    | 0 => {{0}, Set.univ}
    | 1 => {Set.univ}⟩

instance : frame_2_138.ContainsUnit := ⟨by
  ext y; fin_cases y <;> simp [Frame.box, frame_2_138, Set.Fin2.eq_univ, Set.ext_iff]⟩

instance : frame_2_138.IsReflexive where
  refl X := by
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;>
      intro y hy <;> fin_cases y <;>
        simp_all [Frame.box, frame_2_138, Set.Fin2.eq_univ, Set.ext_iff]

instance : frame_2_138.IsMonotonic where
  mono X Y := by
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;>
      rcases Set.Fin2.all_cases Y with rfl | rfl | rfl | rfl <;>
        intro y hy <;> fin_cases y <;>
          simp_all [Frame.box, frame_2_138, Set.Fin2.eq_univ, Set.ext_iff]

instance : frame_2_138.IsRegular where
  regular X Y := by
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;>
      rcases Set.Fin2.all_cases Y with rfl | rfl | rfl | rfl <;>
        intro y hy <;> fin_cases y <;>
          simp_all [Frame.box, frame_2_138, Set.Fin2.eq_univ, Set.ext_iff]

instance : frame_2_138.IsSerial where
  serial X := by
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;>
      intro y hy <;> fin_cases y <;>
        simp_all [Frame.box, Frame.dia, frame_2_138, Set.Fin2.eq_univ, Set.ext_iff]

instance : frame_2_138.IsTransitive where
  trans X := by
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    have hboxE : frame_2_138.box (∅ : Set (Fin 2)) = ∅ := by
      ext y; fin_cases y <;> simp [Frame.box, frame_2_138, Set.Fin2.eq_univ, Set.ext_iff]
    have hbox0 : frame_2_138.box ({0} : Set (Fin 2)) = {0} := by
      ext y; fin_cases y <;> simp [Frame.box, frame_2_138, Set.Fin2.eq_univ, Set.ext_iff]
    have hbox1 : frame_2_138.box ({1} : Set (Fin 2)) = ∅ := by
      ext y; fin_cases y <;> simp [Frame.box, frame_2_138, Set.Fin2.eq_univ, Set.ext_iff]
    have hboxU : frame_2_138.box ({0, 1} : Set (Fin 2)) = {0, 1} := by
      ext y; fin_cases y <;> simp [Frame.box, frame_2_138, Set.Fin2.eq_univ, Set.ext_iff]
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl
    · rw [hboxU, hboxU]
    · rw [hbox0, hbox0]
    · rw [hbox1, hboxE]
    · rw [hboxE, hboxE]

lemma frame_2_138.not_isSymmetric : ¬frame_2_138.IsSymmetric := by
  intro hS
  have hdia : frame_2_138.dia ({1} : Set (Fin 2)) = {1} := by
    ext y; fin_cases y <;> simp [Frame.dia, Frame.box, frame_2_138, Set.Fin2.eq_univ, Set.ext_iff]
  have hbox : frame_2_138.box ({1} : Set (Fin 2)) = ∅ := by
    ext y; fin_cases y <;> simp [Frame.box, frame_2_138, Set.Fin2.eq_univ, Set.ext_iff]
  have h2 := hS.symm ({1} : Set (Fin 2))
    (show (1 : Fin 2) ∈ ({1} : Set (Fin 2)) by simp)
  rw [hdia, hbox] at h2
  simp at h2

lemma frame_2_138.not_valid_axiomB :
    ¬frame_2_138 ⊧ (Axioms.B #0 : Formula ℕ) :=
  fun h => frame_2_138.not_isSymmetric (isSymmetric_of_valid_axiomB h)

lemma frame_2_138.not_isEuclidean : ¬frame_2_138.IsEuclidean := by
  intro hE
  have hdia : frame_2_138.dia ({1} : Set (Fin 2)) = {1} := by
    ext y; fin_cases y <;> simp [Frame.dia, Frame.box, frame_2_138, Set.Fin2.eq_univ, Set.ext_iff]
  have hbox : frame_2_138.box ({1} : Set (Fin 2)) = ∅ := by
    ext y; fin_cases y <;> simp [Frame.box, frame_2_138, Set.Fin2.eq_univ, Set.ext_iff]
  have h1 : (1 : Fin 2) ∈ frame_2_138.dia ({1} : Set (Fin 2)) := by
    rw [hdia]; rfl
  have h2 := hE.eucl ({1} : Set (Fin 2)) h1
  rw [hdia, hbox] at h2
  simp at h2

lemma frame_2_138.not_valid_axiomFive :
    ¬frame_2_138 ⊧ (Axioms.Five #0 : Formula ℕ) :=
  fun h => frame_2_138.not_isEuclidean (isEuclidean_of_valid_axiomFive h)

end
