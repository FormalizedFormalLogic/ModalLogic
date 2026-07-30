module

public import Neighborhood.Semantics.AxiomM
public import Neighborhood.Semantics.AxiomC
public import Neighborhood.Semantics.AxiomN
public import Neighborhood.Semantics.AxiomP
public import Neighborhood.Semantics.AxiomK
public import Neighborhood.Semantics.AxiomGeach

@[expose] public section

variable {α : Type u}

abbrev frame_2_170 : Frame (Fin 2) := ⟨fun _ => {{(1 : Fin 2)}, Set.univ}⟩

lemma frame_2_170.not_isReflexive :
    ¬frame_2_170.IsReflexive := by
  intro hR
  have h1 : (0 : Fin 2) ∈ frame_2_170.box ({1} : Set (Fin 2)) := by
    simp [Frame.box, frame_2_170]
  exact absurd (frame_2_170.refl h1) (by simp)

lemma frame_2_170.not_valid_axiomT :
    ¬frame_2_170 ⊧ (Axioms.T #0 : Formula ℕ) :=
  fun h => frame_2_170.not_isReflexive (isReflexive_of_valid_axiomT h)

lemma frame_2_170.not_isSymmetric : ¬frame_2_170.IsSymmetric := fun hS => by
  have h := hS.symm ({0} : Set (Fin 2))
  have hbox1 : frame_2_170.box ({1} : Set (Fin 2)) = Set.univ := by
    ext x; simp [Frame.box, frame_2_170]
  have hdia : frame_2_170.dia ({0} : Set (Fin 2)) = ∅ := by
    simp [Frame.dia, hbox1]
  have hbox : frame_2_170.box (∅ : Set (Fin 2)) = ∅ := by
    ext x; simp [Frame.box, frame_2_170, Set.ext_iff]
  rw [hdia, hbox] at h
  exact absurd (h (show (0 : Fin 2) ∈ ({0} : Set (Fin 2)) by simp)) (by simp)

lemma frame_2_170.not_valid_axiomB :
    ¬frame_2_170 ⊧ (Axioms.B #0 : Formula ℕ) :=
  fun h => frame_2_170.not_isSymmetric (isSymmetric_of_valid_axiomB h)

instance : frame_2_170.ContainsUnit := ⟨by
  ext x; simp [Frame.box, frame_2_170]⟩

instance : frame_2_170.IsMonotonic where
  mono X Y w hw := by
    simp only [Frame.box, frame_2_170, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw ⊢
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;>
      rcases Set.Fin2.all_cases Y with rfl | rfl | rfl | rfl <;>
      simp_all [Set.ext_iff]

instance : frame_2_170.IsRegular where
  regular X Y := by
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;>
      rcases Set.Fin2.all_cases Y with rfl | rfl | rfl | rfl <;>
        intro w hw <;>
          simp_all [Frame.box, frame_2_170, Set.ext_iff]

instance : frame_2_170.IsSerial where
  serial X := by
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;>
      intro w hw <;>
        simp_all [Frame.box, Frame.dia, frame_2_170, Set.ext_iff]

instance : frame_2_170.IsEuclidean where
  eucl X := by
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;>
      intro w hw <;>
        simp_all [Frame.box, Frame.dia, frame_2_170, Set.ext_iff]

instance : frame_2_170.IsTransitive where
  trans X := by
    intro x hx
    simp only [Frame.box, frame_2_170, Set.mem_setOf_eq,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    have hbox : frame_2_170.box X = Set.univ := by
      ext y
      simp only [Frame.box, frame_2_170, Set.mem_setOf_eq,
        Set.mem_univ, iff_true]
      rcases hx with rfl | rfl <;> simp
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq, hbox]
    simp [Frame.box, frame_2_170]

end
