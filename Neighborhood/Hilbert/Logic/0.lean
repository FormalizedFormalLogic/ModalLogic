module

public import Neighborhood.Hilbert.Basic

@[expose] public section

variable {α : Type u}

abbrev LogicE : Logic α := Hilbert ∅

end
