module

public import Neighborhood.Logic.Logic.ENKD

@[expose] public section

variable {α : Type u}

namespace LogicENKP

/-- `ENKP` and `ENKD` axiomatise the same logic: `D` is derivable from `K` and `P`, while
conversely `P` is derivable from `N` and `D`. -/
theorem eq_LogicENKD : (@LogicENKP α) = LogicENKD := by
  hilbert_eq_axioms

end LogicENKP

end
