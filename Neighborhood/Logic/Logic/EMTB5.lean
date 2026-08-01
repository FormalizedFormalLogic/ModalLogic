module

public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEMTB5

/-- The axiom scheme `B` is redundant over `M`, `T`, and `5`. -/
theorem eq_LogicEMT5 : (@LogicEMTB5 α) = LogicEMT5 := by
  hilbert_eq_axioms

end LogicEMTB5

end
