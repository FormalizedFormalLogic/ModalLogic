module

public import Neighborhood.Semantics.AxiomM
public import Neighborhood.Semantics.AxiomC
public import Neighborhood.Semantics.AxiomN
public import Neighborhood.Semantics.AxiomP
public import Neighborhood.Semantics.AxiomK
public import Neighborhood.Semantics.AxiomGeach

@[expose] public section

variable {α : Type u}

abbrev frame_1_0 : Frame (Fin 1) := ⟨fun _ => ∅⟩

@[simp]
lemma frame_1_0.not_valid_axiomN :
    ¬frame_1_0 ⊧ (Axioms.N : Formula α) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun _ => ∅, 0, by simp [NotForces, Forces, Frame.box]⟩

instance : frame_1_0.IsRegular := ⟨by simp [Frame.box, frame_1_0]⟩

instance : frame_1_0.IsMonotonic where
  mono := by simp_all [frame_1_0, Frame.box]

instance : frame_1_0.IsTransitive where
  trans X := by simp [Frame.box]

instance : frame_1_0.IsSerial where
  serial X x hx := by simp [Frame.box, frame_1_0] at hx

instance : frame_1_0.IsReflexive :=
  ⟨fun X => by simp [Frame.box, frame_1_0]⟩

instance : frame_1_0.NotContainsEmpty := ⟨by simp⟩

lemma frame_1_0.not_isSymmetric : ¬frame_1_0.IsSymmetric := fun hS => by
  have h := hS.symm ({0} : Set (Fin 1))
  have hdia : frame_1_0.dia ({0} : Set (Fin 1)) = Set.univ := by
    ext x; simp [Frame.dia, Frame.box, frame_1_0]
  have hbox : frame_1_0.box (Set.univ : Set (Fin 1)) = ∅ := by
    ext x; simp [Frame.box, frame_1_0]
  rw [hdia, hbox] at h
  exact absurd (h (show (0 : Fin 1) ∈ ({0} : Set (Fin 1)) by simp)) (by simp)

lemma frame_1_0.not_valid_axiomB :
    ¬frame_1_0 ⊧ (Axioms.B #0 : Formula ℕ) :=
  fun h => frame_1_0.not_isSymmetric (isSymmetric_of_valid_axiomB h)

lemma frame_1_0.not_isEuclidean : ¬frame_1_0.IsEuclidean := fun hE => by
  have h := hE.eucl ({0} : Set (Fin 1))
  have hdia : frame_1_0.dia ({0} : Set (Fin 1)) = Set.univ := by
    ext x; simp [Frame.dia, Frame.box, frame_1_0]
  have hbox : frame_1_0.box (Set.univ : Set (Fin 1)) = ∅ := by
    ext x; simp [Frame.box, frame_1_0]
  rw [hdia, hbox] at h
  exact absurd (show Set.univ ⊆ (∅ : Set (Fin 1)) from h) (by simp)

lemma frame_1_0.not_valid_axiomFive :
    ¬frame_1_0 ⊧ (Axioms.Five #0 : Formula ℕ) :=
  fun h => frame_1_0.not_isEuclidean (isEuclidean_of_valid_axiomFive h)

end
