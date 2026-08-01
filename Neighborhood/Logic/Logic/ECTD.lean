module

public import Neighborhood.Logic.Logic.ECT

@[expose] public section

variable {α : Type u}

namespace LogicECTD

/-- The axiom scheme `D` is redundant over `C` and `T`. -/
theorem eq_LogicECT : (@LogicECTD α) = LogicECT := by
  hilbert_eq_axioms

end LogicECTD

end
