module

public import Neighborhood.Logic.Logic.ENT

@[expose] public section

variable {α : Type u}

namespace LogicENTD

/-- The axiom scheme `D` is redundant over `N` and `T`. -/
theorem eq_LogicENT : (@LogicENTD α) = LogicENT := by
  hilbert_eq_axioms

end LogicENTD

end
