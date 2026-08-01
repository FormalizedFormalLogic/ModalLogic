module

public import Neighborhood.Logic.Logic.EMB4

@[expose] public section

variable {α : Type u}

namespace LogicEKB4

/-- `EKB4` and `EMB4` axiomatise the same logic: `M` is derivable from `K`, `B` and `4`, while
conversely `K` is derivable from `M`, `B` and `4`. -/
theorem eq_LogicEMB4 : (@LogicEKB4 α) = LogicEMB4 := by
  hilbert_eq_axioms

end LogicEKB4

end
