module

public import Neighborhood.Logic.Logic.ECT5

@[expose] public section

variable {α : Type u}

namespace LogicECNTB5

/-- The axiom scheme `N` and the axiom scheme `B` are redundant over `C`, `T`, and `5`. -/
theorem eq_LogicECT5 : (@LogicECNTB5 α) = LogicECT5 := by
  hilbert_eq_axioms

end LogicECNTB5

end
