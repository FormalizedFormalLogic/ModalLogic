module

public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEMNDB5

/-- Over `M`, the axiom schemes `N`, `D`, `B` and `5` axiomatise the same logic
as `T` and `5`. -/
theorem eq_LogicEMT5 : (@LogicEMNDB5 α) = LogicEMT5 := by
  hilbert_eq_axioms

end LogicEMNDB5

end
