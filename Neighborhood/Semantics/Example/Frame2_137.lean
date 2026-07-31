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
variable {a b : α}

abbrev frame_2_137 : Frame (Fin 2) :=
  ⟨fun w => match w with
    | 0 => {∅, Set.univ}
    | 1 => {Set.univ}⟩

instance : frame_2_137.ContainsUnit := ⟨by
  ext x; match x with | 0 | 1 => simp [Frame.box, frame_2_137]⟩

instance : frame_2_137.IsRegular where
  regular X Y := by
    intro x hx
    simp only [Frame.box, frame_2_137, Set.mem_setOf_eq] at hx ⊢
    match x with
    | 0 =>
      rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;>
        rcases Set.Fin2.all_cases Y with rfl | rfl | rfl | rfl <;>
        simp_all
    | 1 =>
      rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;>
        rcases Set.Fin2.all_cases Y with rfl | rfl | rfl | rfl <;>
        simp_all

lemma frame_2_137.not_isTransitive : ¬frame_2_137.IsTransitive := by
  intro hT
  have hbox0 : frame_2_137.box (∅ : Set (Fin 2)) = {0} := by
    ext y; fin_cases y <;> simp [Frame.box, frame_2_137, Set.ext_iff]
  have hbox1 : frame_2_137.box ({0} : Set (Fin 2)) = ∅ := by
    ext y; fin_cases y <;> simp [Frame.box, frame_2_137, Set.ext_iff]
  have hiter : frame_2_137.box^[2] (∅ : Set (Fin 2)) = ∅ := by
    show frame_2_137.box (frame_2_137.box ∅) = ∅
    rw [hbox0, hbox1]
  have h1 : (0 : Fin 2) ∈ frame_2_137.box (∅ : Set (Fin 2)) := by
    rw [hbox0]; rfl
  have h2 := hT.trans (∅ : Set (Fin 2)) h1
  rw [hiter] at h2
  simp at h2

lemma frame_2_137.not_valid_axiomFour :
    ¬frame_2_137 ⊧ (Axioms.Four #a : Formula α) :=
  fun h => frame_2_137.not_isTransitive (isTransitive_of_valid_axiomFour h)

lemma frame_2_137.not_isEuclidean : ¬frame_2_137.IsEuclidean := by
  intro hE
  have hdia : frame_2_137.dia (Set.univ : Set (Fin 2)) = {1} := by
    ext y; fin_cases y <;> simp [Frame.dia, Frame.box, frame_2_137, Set.ext_iff]
  have hbox : frame_2_137.box ({1} : Set (Fin 2)) = ∅ := by
    ext y; fin_cases y <;> simp [Frame.box, frame_2_137, Set.ext_iff]
  have h1 : (1 : Fin 2) ∈ frame_2_137.dia (Set.univ : Set (Fin 2)) := by
    rw [hdia]; rfl
  have h2 := hE.eucl (Set.univ : Set (Fin 2)) h1
  rw [hdia, hbox] at h2
  simp at h2

lemma frame_2_137.not_valid_axiomFive :
    ¬frame_2_137 ⊧ (Axioms.Five #a : Formula α) :=
  fun h => frame_2_137.not_isEuclidean (isEuclidean_of_valid_axiomFive h)

lemma frame_2_137.not_isSymmetric : ¬frame_2_137.IsSymmetric := by
  intro hS
  have hdia : frame_2_137.dia (Set.univ : Set (Fin 2)) = {1} := by
    ext y; fin_cases y <;> simp [Frame.dia, Frame.box, frame_2_137, Set.ext_iff]
  have hbox : frame_2_137.box ({1} : Set (Fin 2)) = ∅ := by
    ext y; fin_cases y <;> simp [Frame.box, frame_2_137, Set.ext_iff]
  have h2 := hS.symm (Set.univ : Set (Fin 2))
    (show (0 : Fin 2) ∈ (Set.univ : Set (Fin 2)) by simp)
  rw [hdia, hbox] at h2
  simp at h2

lemma frame_2_137.not_valid_axiomB :
    ¬frame_2_137 ⊧ (Axioms.B #a : Formula α) :=
  fun h => frame_2_137.not_isSymmetric (isSymmetric_of_valid_axiomB h)

@[simp]
lemma frame_2_137.not_valid_axiomM [DecidableEq α] (hab : a ≠ b) :
    ¬frame_2_137 ⊧ (Axioms.M #a #b : Formula α) := fun h => by
  have h0 := h (fun c => if c = a then {0} else if c = b then {1} else Set.univ) 0
  simp [Forces, Frame.box, Set.ext_iff, Ne.symm hab] at h0

end
