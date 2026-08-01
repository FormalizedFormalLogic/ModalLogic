module

public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEMNTB4

/-- Over `M`, `T`, and `5`, the axiom schemes `N`, `B`, and `4` axiomatise the same logic. -/
theorem eq_LogicEMT5 : (@LogicEMNTB4 α) = LogicEMT5 := by
  hilbert_eq_axioms

end LogicEMNTB4

end
