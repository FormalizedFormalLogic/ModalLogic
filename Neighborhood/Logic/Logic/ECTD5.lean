module

public import Neighborhood.Logic.Logic.ECT5

@[expose] public section

variable {α : Type u}

namespace LogicECTD5

/-- The axiom scheme `D` is redundant over `C`, `T`, and `5`. -/
theorem eq_LogicECT5 : (@LogicECTD5 α) = LogicECT5 := by
  hilbert_eq_axioms

end LogicECTD5

end
