module

public import Neighborhood.Logic.Logic.ECT5

@[expose] public section

variable {α : Type u}

namespace LogicECTB45

/-- The axiom schemes `B` and `Four` are redundant over `C`, `T`, and `Five`. -/
theorem eq_LogicECT5 : (@LogicECTB45 α) = LogicECT5 := by
  hilbert_eq_axioms

end LogicECTB45

end
