module

public import Neighborhood.Logic.Logic.ECT5

@[expose] public section

variable {α : Type u}

namespace LogicECNTB4

/-- Over `C`, the axiom schemes `N`, `T`, `B` and `4` axiomatise the same logic
as `T` and `5`. -/
theorem eq_LogicECT5 : (@LogicECNTB4 α) = LogicECT5 := by
  hilbert_eq_axioms

end LogicECNTB4

end
