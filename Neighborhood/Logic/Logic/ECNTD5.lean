module

public import Neighborhood.Logic.Logic.ECT5

@[expose] public section

variable {α : Type u}

namespace LogicECNTD5

/-- The axiom schemes `N` and `D` are redundant over `C`, `T`, and `Five`. -/
theorem eq_LogicECT5 : (@LogicECNTD5 α) = LogicECT5 := by
  hilbert_eq_axioms

end LogicECNTD5

end
