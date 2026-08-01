module

public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEMTB4

/-- The axiom scheme `B` is redundant over `M`, `T`, and `4`; conversely, `4` is derivable from `M`, `T`, and `B`. -/
theorem eq_LogicEMT5 : (@LogicEMTB4 α) = LogicEMT5 := by
  hilbert_eq_axioms

end LogicEMTB4

end
