module

public import Neighborhood.Logic.Logic.EMCT4

@[expose] public section

variable {α : Type u}

namespace LogicEMCTD4

/-- The axiom scheme `D` is redundant over `M`, `C`, `T` and `4`. -/
theorem eq_LogicEMCT4 : (@LogicEMCTD4 α) = LogicEMCT4 := by
  hilbert_eq_axioms

end LogicEMCTD4

end
