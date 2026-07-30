module

public import Neighborhood.Axioms
public import Neighborhood.Semantics.Basic
public import Neighborhood.Semantics.AxiomM
public import Neighborhood.Semantics.AxiomC
public import Neighborhood.Semantics.AxiomN
public import Neighborhood.Semantics.AxiomP
public import Neighborhood.Semantics.AxiomK
public import Neighborhood.Semantics.AxiomGeach
import Mathlib.Tactic.FinCases

@[expose] public section

variable {α : Type u}

abbrev frame_1_3 : Frame (Fin 1) := ⟨fun _ => Set.univ⟩

instance : frame_1_3.IsMonotonic := ⟨fun X Y => by simp [Frame.box]⟩

instance : frame_1_3.IsTransitive := ⟨fun X => by simp [Frame.box]⟩

instance : frame_1_3.IsSymmetric := ⟨fun X => by simp [Frame.box]⟩

instance : frame_1_3.IsEuclidean := ⟨fun X => by simp [Frame.box, Frame.dia]⟩

lemma frame_1_3.not_isReflexive : ¬frame_1_3.IsReflexive := fun hR => by
  simpa using hR.refl (∅ : Set (Fin 1)) (show (0 : Fin 1) ∈ _ by simp [Frame.box])

@[simp]
lemma frame_1_3.not_valid_axiomT : ¬frame_1_3 ⊧ (Axioms.T #0 : Formula ℕ) :=
  fun h => frame_1_3.not_isReflexive (isReflexive_of_valid_axiomT h)

instance : frame_1_3.ContainsUnit := ⟨by simp [Frame.box]⟩

instance : frame_1_3.IsRegular := ⟨by
  intro X Y; simp [Frame.box, frame_1_3]⟩

lemma frame_1_3.not_isSerial : ¬frame_1_3.IsSerial := by
  intro hS
  have h1 : (0 : Fin 1) ∈ frame_1_3.box (∅ : Set (Fin 1)) := by simp [Frame.box]
  have h2 : (0 : Fin 1) ∉ frame_1_3.dia (∅ : Set (Fin 1)) := by simp [Frame.dia, Frame.box]
  exact h2 (hS.serial ∅ h1)

@[simp]
lemma frame_1_3.not_valid_axiomD : ¬frame_1_3 ⊧ (Axioms.D #0 : Formula ℕ) :=
  fun h => frame_1_3.not_isSerial (isSerial_of_valid_axiomD h)

end
