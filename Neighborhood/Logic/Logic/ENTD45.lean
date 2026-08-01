module

public import Neighborhood.Logic.Logic.ET5

@[expose] public section

variable {α : Type u}

namespace LogicENTD45

/-- Over `ET5`, the axiom schemes `N`, `D`, and `4` are redundant. -/
theorem eq_LogicET5 : (@LogicENTD45 α) = LogicET5 := by
  hilbert_eq_axioms

end LogicENTD45

end
