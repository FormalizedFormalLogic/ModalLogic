module

public import Neighborhood.Logic.Logic.ECT5

@[expose] public section

variable {α : Type u}

namespace LogicECDB4

/-- Over `C`, the axiom schemes `D`, `B`, and `4` axiomatise the same logic as `T` and `5`. -/
theorem eq_LogicECT5 : (@LogicECDB4 α) = LogicECT5 := by
  hilbert_eq_axioms

end LogicECDB4

end
