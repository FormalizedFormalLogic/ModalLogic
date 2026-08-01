module

public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEMNTB5

/-- The axiom schemes `N` and `B` are redundant over `M`, `T` and `5`. -/
theorem eq_LogicEMT5 : (@LogicEMNTB5 α) = LogicEMT5 := by
  hilbert_eq_axioms

end LogicEMNTB5

end
