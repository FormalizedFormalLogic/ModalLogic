module

public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEMCDB4

/-- Over `M`, the axiom schemes `C`, `D`, `B` and `4` axiomatise the same logic
as `T` and `5`. -/
theorem eq_LogicEMT5 : (@LogicEMCDB4 α) = LogicEMT5 := by
  hilbert_eq_axioms

end LogicEMCDB4

end
