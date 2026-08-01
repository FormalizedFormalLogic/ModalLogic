module

public import Neighborhood.Logic.Logic.EMB

@[expose] public section

variable {α : Type u}

namespace LogicENKB

/-- `ENKB` and `EMB` axiomatise the same logic: `M` is derivable from `K` and `N`, while
conversely `K` is derivable from `M` and `B`. -/
theorem eq_LogicEMB : (@LogicENKB α) = LogicEMB := by
  hilbert_eq_axioms

end LogicENKB

end
