module

public import Neighborhood.Logic.Logic.EMB4

@[expose] public section

variable {α : Type u}

namespace LogicEMB45

/-- The axiom scheme `5` is redundant over `M`, `B`, and `4`. -/
theorem eq_LogicEMB4 : (@LogicEMB45 α) = LogicEMB4 := by
  hilbert_eq_axioms

end LogicEMB45

end
