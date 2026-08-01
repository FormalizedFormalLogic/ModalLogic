module

public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEKT5

/-- `EKT5` and `EMT5` axiomatise the same logic: `M` is derivable from `K`, `T` and `5`, while
conversely `K` is derivable from `M`, `T` and `5`. -/
theorem eq_LogicEMT5 : (@LogicEKT5 α) = LogicEMT5 := by
  hilbert_eq_axioms

end LogicEKT5

end
