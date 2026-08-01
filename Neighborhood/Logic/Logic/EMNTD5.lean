module

public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEMNTD5

/-- The axiom schemes `N` and `D` are redundant over `M`, `T` and `5`. -/
theorem eq_LogicEMT5 : (@LogicEMNTD5 α) = LogicEMT5 := by
  hilbert_eq_axioms

end LogicEMNTD5

end
