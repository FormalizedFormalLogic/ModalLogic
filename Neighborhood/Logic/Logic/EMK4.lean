module

public import Neighborhood.Logic.Logic.EMC4

@[expose] public section

variable {α : Type u}

namespace LogicEMK4

/-- Over `EM4`, the axiom scheme `K` and the axiom scheme `C` axiomatise the same logic. -/
theorem eq_LogicEMC4 : (@LogicEMK4 α) = LogicEMC4 := by
  hilbert_eq_axioms

end LogicEMK4

end
