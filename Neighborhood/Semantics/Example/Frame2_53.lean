module

public import Neighborhood.Semantics.AxiomM
public import Neighborhood.Semantics.AxiomC
public import Neighborhood.Semantics.AxiomN
public import Neighborhood.Semantics.AxiomP
public import Neighborhood.Semantics.AxiomK
public import Neighborhood.Semantics.AxiomGeach

@[expose] public section

variable {α : Type u}

abbrev frame_2_53 : Frame (Fin 2) :=
  ⟨fun w => match w with | 0 => {∅, {1}} | 1 => {∅, {0}}⟩

instance : frame_2_53.IsSerial where
  serial X x := by
    match x with
    | 0 | 1 => rintro (rfl | rfl) <;> simp [Frame.dia, Frame.box]; tauto_set

end
