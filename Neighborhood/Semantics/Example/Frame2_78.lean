module

public import Neighborhood.Semantics.AxiomM
public import Neighborhood.Semantics.AxiomC
public import Neighborhood.Semantics.AxiomN
public import Neighborhood.Semantics.AxiomP
public import Neighborhood.Semantics.AxiomK
public import Neighborhood.Semantics.AxiomGeach

@[expose] public section

variable {α : Type u}

abbrev frame_2_78 : Frame (Fin 2) :=
  ⟨fun w => match w with | 0 => {{0}} | 1 => {{0}, {1}, {0, 1}}⟩

lemma frame_2_78.not_isSerial : ¬frame_2_78.IsSerial := by
  intro hS
  have h1 : (1 : Fin 2) ∈ frame_2_78.box {1} := by simp [Frame.box]
  have h2 : (1 : Fin 2) ∉ frame_2_78.dia {1} := by simp [Frame.dia, Frame.box]
  exact h2 (hS.serial {1} h1)

instance : frame_2_78.NotContainsEmpty :=
  ⟨fun x => by match x with | 0 => simp | 1 => simp; tauto_set⟩

lemma frame_2_78.not_valid_axiomC :
    ¬frame_2_78 ⊧ (Axioms.C #0 #1 : Formula ℕ) := fun h => by
  have h1 := h (fun a => match a with | 0 => {0} | 1 => {1} | _ => Set.univ) 1
  simp [Forces, Frame.box, Set.ext_iff, frame_2_78] at h1

lemma frame_2_78.not_valid_axiomM :
    ¬frame_2_78 ⊧ (Axioms.M #0 #1 : Formula ℕ) := fun h => by
  have h0 := h (fun a => match a with | 0 => {0, 1} | 1 => {0} | _ => Set.univ) 0
  simp [Forces, Frame.box, Set.ext_iff, frame_2_78] at h0

lemma frame_2_78.not_isReflexive : ¬frame_2_78.IsReflexive := by
  intro hR
  have h1 : (1 : Fin 2) ∈ frame_2_78.box ({0} : Set (Fin 2)) := by simp [Frame.box, frame_2_78]
  exact absurd (frame_2_78.refl h1) (by simp)

lemma frame_2_78.not_valid_axiomT :
    ¬frame_2_78 ⊧ (Axioms.T #0 : Formula ℕ) :=
  fun h => frame_2_78.not_isReflexive (isReflexive_of_valid_axiomT h)

end
