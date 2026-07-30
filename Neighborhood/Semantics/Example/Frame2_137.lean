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

abbrev frame_2_137 : Frame (Fin 2) :=
  ⟨fun w => match w with
    | 0 => {∅, Set.univ}
    | 1 => {Set.univ}⟩

instance : frame_2_137.ContainsUnit := ⟨by
  ext x; match x with | 0 | 1 => simp [Frame.box, frame_2_137]⟩

@[simp]
lemma frame_2_137.not_valid_axiomM :
    ¬frame_2_137 ⊧ (Axioms.M #0 #1 : Formula ℕ) := fun h => by
  have h0 := h (fun a => match a with | 0 => {0} | 1 => {1} | _ => Set.univ) 0
  simp [Forces, Frame.box, Set.ext_iff] at h0

end
