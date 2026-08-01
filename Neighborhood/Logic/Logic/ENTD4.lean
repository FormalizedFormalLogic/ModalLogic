module

public import Neighborhood.Logic.Logic.ENT4

@[expose] public section

variable {α : Type u}

namespace LogicENTD4

/-- The axiom scheme `D` is redundant over `N`, `T` and `4`. -/
theorem eq_LogicENT4 : (@LogicENTD4 α) = LogicENT4 := by
  hilbert_eq_axioms

end LogicENTD4

end
