module

public import Neighborhood.Logic.Logic.ECT5

@[expose] public section

variable {α : Type u}

namespace LogicECNDB4

/-- Over `ECT5`, the axiom schemes `N`, `D`, and `B` are redundant. -/
theorem eq_LogicECT5 : (@LogicECNDB4 α) = LogicECT5 := by
  hilbert_eq_axioms

end LogicECNDB4

end
