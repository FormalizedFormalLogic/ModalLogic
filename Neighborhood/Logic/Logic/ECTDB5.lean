module

public import Neighborhood.Logic.Logic.ECT5

@[expose] public section

variable {α : Type u}

namespace LogicECTDB5

/-- The axiom schemes `D` and `B` are redundant over `C`, `T` and `5`. -/
theorem eq_LogicECT5 : (@LogicECTDB5 α) = LogicECT5 := by
  hilbert_eq_axioms

end LogicECTDB5

end
