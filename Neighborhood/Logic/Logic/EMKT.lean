module

public import Neighborhood.Logic.Logic.EMCT

@[expose] public section

variable {α : Type u}

namespace LogicEMKT

/-- Over `EMT`, the axiom scheme `K` and the axiom scheme `C` axiomatise the same logic. -/
theorem eq_LogicEMCT : (@LogicEMKT α) = LogicEMCT := by
  hilbert_eq_axioms

end LogicEMKT

end
