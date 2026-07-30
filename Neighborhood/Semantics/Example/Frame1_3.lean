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

end
