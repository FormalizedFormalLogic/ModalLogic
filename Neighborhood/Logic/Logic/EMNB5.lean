module

public import Neighborhood.Logic.Logic.EMB4

@[expose] public section

variable {α : Type u}

namespace LogicEMNB5

/-- The axiom scheme `N` is redundant over `M`, `B`, and `5`; conversely, `5` is derivable from `M`, `N`, and `B`. -/
theorem eq_LogicEMB4 : (@LogicEMNB5 α) = LogicEMB4 := by
  hilbert_eq_axioms

end LogicEMNB5

end
