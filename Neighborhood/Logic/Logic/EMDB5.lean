module

public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEMDB5

/-- Over `M`, `D`, `B`, and `5` axiomatise the same logic as `M`, `T`, and `5`. -/
theorem eq_LogicEMT5 : (@LogicEMDB5 α) = LogicEMT5 := by
  hilbert_eq_axioms

end LogicEMDB5

end
