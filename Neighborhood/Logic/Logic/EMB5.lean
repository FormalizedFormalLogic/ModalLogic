module

public import Neighborhood.Logic.Logic.EMB4

@[expose] public section

variable {α : Type u}

namespace LogicEMB5

/-- Over `EMB`, the axiom scheme `5` and the axiom scheme `4` axiomatise the same logic. -/
theorem eq_LogicEMB4 : (@LogicEMB5 α) = LogicEMB4 := by
  hilbert_eq_axioms

end LogicEMB5

end
