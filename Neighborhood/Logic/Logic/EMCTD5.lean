module

public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEMCTD5

/-- The axiom scheme `C` and the axiom scheme `D` are redundant over `M`, `T`, and `5`. -/
theorem eq_LogicEMT5 : (@LogicEMCTD5 α) = LogicEMT5 := by
  hilbert_eq_axioms

end LogicEMCTD5

end
