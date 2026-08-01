module

public import Neighborhood.Logic.Logic.ECT5

@[expose] public section

variable {α : Type u}

namespace LogicECDB45

/-- Over `C`, the axiom schemes `D`, `B`, `4` and `5` axiomatise the same logic
as `T` and `5`. -/
theorem eq_LogicECT5 : (@LogicECDB45 α) = LogicECT5 := by
  hilbert_eq_axioms

end LogicECDB45

end
