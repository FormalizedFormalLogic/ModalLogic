module

public import Neighborhood.Logic.Logic.ECT5

@[expose] public section

variable {α : Type u}

namespace LogicECTD45

/-- Over `ECT5`, the axiom schemes `D` and `4` are redundant. -/
theorem eq_LogicECT5 : (@LogicECTD45 α) = LogicECT5 := by
  hilbert_eq_axioms

end LogicECTD45

end
