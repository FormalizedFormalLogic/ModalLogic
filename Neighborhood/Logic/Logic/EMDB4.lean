module

public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEMDB4

/-- Over `M`, the axiom schemes `D`, `B` and `4` axiomatise the same logic as `T` and `5`. -/
theorem eq_LogicEMT5 : (@LogicEMDB4 α) = LogicEMT5 := by
  hilbert_eq_axioms

end LogicEMDB4

end
