module

public import Neighborhood.Logic.Logic.EMCT

@[expose] public section

variable {α : Type u}

namespace LogicEMCTD

/-- The axiom scheme `D` is redundant over `M`, `C`, and `T`. -/
theorem eq_LogicEMCT : (@LogicEMCTD α) = LogicEMCT := by
  hilbert_eq_axioms

end LogicEMCTD

end
