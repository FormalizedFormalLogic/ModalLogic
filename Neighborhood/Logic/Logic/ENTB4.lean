module

public import Neighborhood.Logic.Logic.ET5

@[expose] public section

variable {α : Type u}

namespace LogicENTB4

/-- Over `N`, the axiom schemes `T`, `B`, and `4` axiomatise the same logic as `T` and `5`. -/
theorem eq_LogicET5 : (@LogicENTB4 α) = LogicET5 := by
  hilbert_eq_axioms

end LogicENTB4

end
