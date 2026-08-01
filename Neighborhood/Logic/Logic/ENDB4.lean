module

public import Neighborhood.Logic.Logic.ET5

@[expose] public section

variable {α : Type u}

namespace LogicENDB4

/-- Over `N`, `D`, `B`, and `4` axiomatise the same logic as `T` and `5`. -/
theorem eq_LogicET5 : (@LogicENDB4 α) = LogicET5 := by
  hilbert_eq_axioms

end LogicENDB4

end
