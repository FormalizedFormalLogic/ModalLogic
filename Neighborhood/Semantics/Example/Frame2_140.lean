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

abbrev frame_2_140 : Frame (Fin 2) :=
  ⟨fun w => match w with
    | 0 => {{1}, Set.univ}
    | 1 => {Set.univ}⟩

instance : frame_2_140.ContainsUnit := ⟨by
  ext y; fin_cases y <;> simp [Frame.box, frame_2_140, Set.Fin2.eq_univ, Set.ext_iff]⟩

instance : frame_2_140.IsMonotonic where
  mono X Y := by
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;>
      rcases Set.Fin2.all_cases Y with rfl | rfl | rfl | rfl <;>
        intro y hy <;> fin_cases y <;>
          simp_all [Frame.box, frame_2_140, Set.Fin2.eq_univ, Set.ext_iff]

instance : frame_2_140.IsSymmetric where
  symm X := by
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;>
      intro y hy <;> fin_cases y <;>
        simp_all [Frame.box, Frame.dia, frame_2_140, Set.Fin2.eq_univ, Set.ext_iff]

instance : frame_2_140.IsRegular where
  regular X Y := by
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;>
      rcases Set.Fin2.all_cases Y with rfl | rfl | rfl | rfl <;>
        intro y hy <;> fin_cases y <;>
          simp_all [Frame.box, frame_2_140, Set.Fin2.eq_univ, Set.ext_iff]

instance : frame_2_140.IsSerial where
  serial X := by
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;>
      intro y hy <;> fin_cases y <;>
        simp_all [Frame.box, Frame.dia, frame_2_140, Set.Fin2.eq_univ, Set.ext_iff]

lemma frame_2_140.not_isReflexive : ¬frame_2_140.IsReflexive := by
  intro hR
  have h1 : (0 : Fin 2) ∈ frame_2_140.box ({1} : Set (Fin 2)) := by
    simp [Frame.box, frame_2_140]
  exact absurd (frame_2_140.refl h1) (by simp)

lemma frame_2_140.not_valid_axiomT :
    ¬frame_2_140 ⊧ (Axioms.T #a : Formula α) :=
  fun h => frame_2_140.not_isReflexive (isReflexive_of_valid_axiomT h)

lemma frame_2_140.not_isEuclidean : ¬frame_2_140.IsEuclidean := by
  intro hE
  have hbox1 : frame_2_140.box ({1} : Set (Fin 2)) = {0} := by
    ext y; fin_cases y <;> simp [Frame.box, frame_2_140, Set.Fin2.eq_univ, Set.ext_iff]
  have hdia : frame_2_140.dia ({0} : Set (Fin 2)) = {1} := by
    ext y; fin_cases y <;> simp [Frame.dia, Frame.box, frame_2_140, Set.Fin2.eq_univ, Set.ext_iff]
  have h1 : (1 : Fin 2) ∈ frame_2_140.dia ({0} : Set (Fin 2)) := by
    rw [hdia]; rfl
  have h2 := hE.eucl ({0} : Set (Fin 2)) h1
  rw [hdia, hbox1] at h2
  simp at h2

lemma frame_2_140.not_valid_axiomFive :
    ¬frame_2_140 ⊧ (Axioms.Five #a : Formula α) :=
  fun h => frame_2_140.not_isEuclidean (isEuclidean_of_valid_axiomFive h)

lemma frame_2_140.not_isTransitive : ¬frame_2_140.IsTransitive := by
  intro hT
  have hbox0 : frame_2_140.box ({0} : Set (Fin 2)) = ∅ := by
    ext y; fin_cases y <;> simp [Frame.box, frame_2_140, Set.Fin2.eq_univ, Set.ext_iff]
  have hbox1 : frame_2_140.box ({1} : Set (Fin 2)) = {0} := by
    ext y; fin_cases y <;> simp [Frame.box, frame_2_140, Set.Fin2.eq_univ, Set.ext_iff]
  have hiter : frame_2_140.box^[2] ({1} : Set (Fin 2)) = ∅ := by
    show frame_2_140.box (frame_2_140.box {1}) = ∅
    rw [hbox1, hbox0]
  have h1 : (0 : Fin 2) ∈ frame_2_140.box ({1} : Set (Fin 2)) := by
    rw [hbox1]; rfl
  have h2 := hT.trans ({1} : Set (Fin 2)) h1
  rw [hiter] at h2
  simp at h2

lemma frame_2_140.not_valid_axiomFour :
    ¬frame_2_140 ⊧ (Axioms.Four #a : Formula α) :=
  fun h => frame_2_140.not_isTransitive (isTransitive_of_valid_axiomFour h)

end
