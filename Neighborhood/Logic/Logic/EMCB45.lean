module

public import Neighborhood.Logic.Logic.EMB4

@[expose] public section

variable {α : Type u}

namespace LogicEMCB45

/-- The axiom schemes `C` and `5` are redundant over `M`, `B` and `4`. -/
theorem eq_LogicEMB4 : (@LogicEMCB45 α) = LogicEMB4 := by
  hilbert_eq_axioms

end LogicEMCB45

end
