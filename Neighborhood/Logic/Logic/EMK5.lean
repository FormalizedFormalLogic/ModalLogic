module

public import Neighborhood.Logic.Logic.EMC5

@[expose] public section

variable {α : Type u}

namespace LogicEMK5

/-- Over `EM5`, the axiom scheme `K` and the axiom scheme `C` axiomatise the same logic. -/
theorem eq_LogicEMC5 : (@LogicEMK5 α) = LogicEMC5 := by
  hilbert_eq_axioms

end LogicEMK5

end
