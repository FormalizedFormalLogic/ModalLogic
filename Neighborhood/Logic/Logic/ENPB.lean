module

public import Neighborhood.Logic.Logic.EPB

@[expose] public section

variable {α : Type u}

namespace LogicENPB

/-- The axiom `N` is redundant over `P` and `B`. -/
theorem eq_LogicEPB : (@LogicENPB α) = LogicEPB := by
  hilbert_eq_axioms

end LogicENPB

end
