module

public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEMCTB4

/-- The axiom schemes `C` and `B` are redundant over `M`, `T` and `5`. -/
theorem eq_LogicEMT5 : (@LogicEMCTB4 α) = LogicEMT5 := by
  hilbert_eq_axioms

end LogicEMCTB4

end
