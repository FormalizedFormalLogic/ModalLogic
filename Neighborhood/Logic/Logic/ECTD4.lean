module

public import Neighborhood.Logic.Logic.ECT4

@[expose] public section

variable {α : Type u}

namespace LogicECTD4

/-- The axiom scheme `D` is redundant over `C`, `T`, and `4`. -/
theorem eq_LogicECT4 : (@LogicECTD4 α) = LogicECT4 := by
  hilbert_eq_axioms

end LogicECTD4

end
