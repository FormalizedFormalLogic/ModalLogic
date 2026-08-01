module

public import Neighborhood.Logic.Logic.ET5

@[expose] public section

variable {α : Type u}

namespace LogicENDB45

/-- Over `N`, the axiom schemes `D`, `B`, `4` and `5` axiomatise the same logic
as `T` and `5`. -/
theorem eq_LogicET5 : (@LogicENDB45 α) = LogicET5 := by
  hilbert_eq_axioms

end LogicENDB45

end
