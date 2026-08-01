module

public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEMCTB5

/-- Over `EMT5`, the axiom schemes `C` and `B` are redundant. -/
theorem eq_LogicEMT5 : (@LogicEMCTB5 α) = LogicEMT5 := by
  hilbert_eq_axioms

end LogicEMCTB5

end
