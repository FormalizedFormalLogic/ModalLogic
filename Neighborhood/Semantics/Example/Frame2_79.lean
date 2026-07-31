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

abbrev frame_2_79 : Frame (Fin 2) :=
  ⟨fun w => match w with
    | 0 => {{0}}
    | 1 => Set.univ⟩

lemma frame_2_79.not_isSerial : ¬frame_2_79.IsSerial := fun hS => by
  have := hS.serial {1} (show (1 : Fin 2) ∈ _ by simp [Frame.box])
  simp [Frame.dia, Frame.box] at this

instance : frame_2_79.IsRegular where
  regular X Y := by
    intro x hx
    simp only [Frame.box, frame_2_79, Set.mem_setOf_eq] at hx ⊢
    match x with
    | 0 =>
      rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;>
        rcases Set.Fin2.all_cases Y with rfl | rfl | rfl | rfl <;>
        simp_all
    | 1 => trivial

instance : frame_2_79.IsEuclidean where
  eucl X := by
    have hbox0 : frame_2_79.box ({0} : Set (Fin 2)) = Set.univ := by
      ext y; fin_cases y <;> simp [Frame.box, frame_2_79]
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl
    · have hdia : frame_2_79.dia ({0, 1} : Set (Fin 2)) = {0} := by
        ext y; fin_cases y <;> simp [Frame.dia, Frame.box, frame_2_79, ← Set.Fin2.eq_univ]
      rw [hdia, hbox0]; exact Set.subset_univ _
    · have hdia : frame_2_79.dia ({0} : Set (Fin 2)) = {0} := by
        ext y; fin_cases y <;> simp [Frame.dia, Frame.box, frame_2_79]
      rw [hdia, hbox0]; exact Set.subset_univ _
    · have hdia : frame_2_79.dia ({1} : Set (Fin 2)) = ∅ := by
        ext y; fin_cases y <;> simp [Frame.dia, Frame.box, frame_2_79]
      rw [hdia]; exact Set.empty_subset _
    · have hne : (Set.univ : Set (Fin 2)) ≠ {0} := Set.Fin2.ne_singleton_univ.symm
      have hdia : frame_2_79.dia (∅ : Set (Fin 2)) = {0} := by
        ext y; fin_cases y <;> simp [Frame.dia, Frame.box, frame_2_79, hne]
      rw [hdia, hbox0]; exact Set.subset_univ _

lemma frame_2_79.not_isTransitive : ¬frame_2_79.IsTransitive := by
  intro hT
  have hbox0 : frame_2_79.box ({0} : Set (Fin 2)) = Set.univ := by
    ext y; fin_cases y <;> simp [Frame.box, frame_2_79]
  have hbox1 : frame_2_79.box (Set.univ : Set (Fin 2)) = {1} := by
    ext y; fin_cases y <;> simp [Frame.box, frame_2_79, Set.ext_iff]
  have hiter : frame_2_79.box^[2] ({0} : Set (Fin 2)) = {1} := by
    show frame_2_79.box (frame_2_79.box {0}) = {1}
    rw [hbox0, hbox1]
  have h1 : (0 : Fin 2) ∈ frame_2_79.box ({0} : Set (Fin 2)) := by
    rw [hbox0]; trivial
  have h2 := hT.trans ({0} : Set (Fin 2)) h1
  rw [hiter] at h2
  simp at h2

lemma frame_2_79.not_valid_axiomFour :
    ¬frame_2_79 ⊧ (Axioms.Four #a : Formula α) :=
  fun h => frame_2_79.not_isTransitive (isTransitive_of_valid_axiomFour h)

end
