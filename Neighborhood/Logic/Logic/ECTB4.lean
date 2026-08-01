module

public import Neighborhood.Logic.Logic.ECT5

@[expose] public section

variable {α : Type u}

namespace LogicECTB4

/-- The axiom scheme `B` is redundant over `C`, `T` and `5`, and the axiom scheme `4` is derivable
over `C`, `T`, `B` and `4`. -/
theorem eq_LogicECT5 : (@LogicECTB4 α) = LogicECT5 := by
  hilbert_eq_axioms

end LogicECTB4

end
