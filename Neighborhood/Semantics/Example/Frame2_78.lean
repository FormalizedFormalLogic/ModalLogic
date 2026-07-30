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

end
