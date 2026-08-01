module

public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEMTB45

/-- The axiom scheme `B` is redundant over `M`, `T`, `4` and `5`. -/
theorem eq_LogicEMT5 : (@LogicEMTB45 α) = LogicEMT5 := by
  hilbert_eq_axioms

end LogicEMTB45

end
