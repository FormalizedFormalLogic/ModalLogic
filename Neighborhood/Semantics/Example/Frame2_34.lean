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

abbrev frame_2_34 : Frame (Fin 2) := ⟨fun _ => {{(1 : Fin 2)}}⟩

lemma frame_2_34.box_empty : frame_2_34.box (∅ : Set (Fin 2)) = ∅ := by
  ext y; fin_cases y <;> simp [Frame.box, frame_2_34]

lemma frame_2_34.box_zero : frame_2_34.box ({0} : Set (Fin 2)) = ∅ := by
  ext y; fin_cases y <;> simp [Frame.box, frame_2_34]

lemma frame_2_34.box_one : frame_2_34.box ({1} : Set (Fin 2)) = Set.univ := by
  ext y; fin_cases y <;> simp [Frame.box, frame_2_34]

lemma frame_2_34.box_univ : frame_2_34.box (Set.univ : Set (Fin 2)) = ∅ := by
  ext y; fin_cases y <;> simp [Frame.box, frame_2_34, Set.ext_iff]

instance : frame_2_34.IsRegular where
  regular X Y := by
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;>
      rcases Set.Fin2.all_cases Y with rfl | rfl | rfl | rfl <;>
        simp [frame_2_34.box_empty, frame_2_34.box_zero, frame_2_34.box_one]

instance : frame_2_34.NotContainsEmpty := ⟨fun x => by simp⟩

lemma frame_2_34.not_isReflexive : ¬frame_2_34.IsReflexive := by
  intro hR
  have h1 : (0 : Fin 2) ∈ frame_2_34.box ({1} : Set (Fin 2)) := by
    rw [frame_2_34.box_one]; trivial
  exact absurd (frame_2_34.refl h1) (by simp)

lemma frame_2_34.not_valid_axiomT :
    ¬frame_2_34 ⊧ (Axioms.T #0 : Formula ℕ) :=
  fun h => frame_2_34.not_isReflexive (isReflexive_of_valid_axiomT h)

lemma frame_2_34.not_valid_axiomM :
    ¬frame_2_34 ⊧ (Axioms.M #0 #1 : Formula ℕ) := fun h => by
  have h0 := h (fun a => match a with | 0 => Set.univ | 1 => {1} | _ => ∅) 0
  simp [Forces, Frame.box, Set.ext_iff, frame_2_34] at h0

end
