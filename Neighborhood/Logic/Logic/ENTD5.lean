module

public import Neighborhood.Logic.Logic.ET5

@[expose] public section

variable {α : Type u}

namespace LogicENTD5

/-- The axiom schemes `N` and `D` are redundant over `T` and `5`. -/
theorem eq_LogicET5 : (@LogicENTD5 α) = LogicET5 := by
  hilbert_eq_axioms

end LogicENTD5

end
