module

public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEMTD5

/-- The axiom scheme `D` is redundant over `M`, `T` and `5`. -/
theorem eq_LogicEMT5 : (@LogicEMTD5 α) = LogicEMT5 := by
  hilbert_eq_axioms

end LogicEMTD5

end
