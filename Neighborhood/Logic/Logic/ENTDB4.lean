module

public import Neighborhood.Logic.Logic.ET5

@[expose] public section

variable {α : Type u}

namespace LogicENTDB4

/-- Over `T` and `5`, the axiom schemes `N`, `D`, `B`, and `4` axiomatise the same logic. -/
theorem eq_LogicET5 : (@LogicENTDB4 α) = LogicET5 := by
  hilbert_eq_axioms

end LogicENTDB4

end
