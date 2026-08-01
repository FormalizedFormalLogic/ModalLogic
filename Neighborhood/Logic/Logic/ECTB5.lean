module

public import Neighborhood.Logic.Logic.ECT5

@[expose] public section

variable {α : Type u}

namespace LogicECTB5

/-- The axiom scheme `B` is redundant over `C`, `T` and `5`. -/
theorem eq_LogicECT5 : (@LogicECTB5 α) = LogicECT5 := by
  hilbert_eq_axioms

end LogicECTB5

end
