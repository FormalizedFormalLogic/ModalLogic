module

public import Neighborhood.Semantics.AxiomM
public import Neighborhood.Semantics.AxiomC
public import Neighborhood.Semantics.AxiomN
public import Neighborhood.Semantics.AxiomP
public import Neighborhood.Semantics.AxiomK
public import Neighborhood.Semantics.AxiomGeach

@[expose] public section

variable {α : Type u}
variable {a b : α}

abbrev frame_2_22 : Frame (Fin 2) :=
  ⟨fun w => match w with
    | 0 => {{0}, {1}}
    | 1 => {∅}⟩

@[simp]
lemma frame_2_22.not_valid_axiomC [DecidableEq α] (hab : a ≠ b) :
    ¬frame_2_22 ⊧ (Axioms.C #a #b : Formula α) := fun h => by
  have h0 := h (fun c => if c = a then {0} else if c = b then {1} else Set.univ) 0
  simp [Forces, Frame.box, Set.ext_iff, Ne.symm hab] at h0

end
