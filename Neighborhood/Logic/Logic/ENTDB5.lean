module

public import Neighborhood.Logic.Logic.ET5

@[expose] public section

variable {α : Type u}

namespace LogicENTDB5

/-- The axiom schemes `N`, `D` and `B` are redundant over `T` and `5`. -/
theorem eq_LogicET5 : (@LogicENTDB5 α) = LogicET5 := by
  hilbert_eq_axioms

end LogicENTDB5

end
