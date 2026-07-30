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

abbrev frame_2_79 : Frame (Fin 2) :=
  ⟨fun w => match w with
    | 0 => {{0}}
    | 1 => Set.univ⟩

lemma frame_2_79.not_isSerial : ¬frame_2_79.IsSerial := fun hS => by
  have := hS.serial {1} (show (1 : Fin 2) ∈ _ by simp [Frame.box])
  simp [Frame.dia, Frame.box] at this

end
