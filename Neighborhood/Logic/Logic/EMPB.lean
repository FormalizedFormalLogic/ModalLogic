module

public import Neighborhood.Logic.Logic.EMDB

@[expose] public section

variable {α : Type u}

namespace LogicEMPB

/-- Over `EMB`, the axiom `P` and the axiom scheme `D` axiomatise the same logic. -/
theorem eq_LogicEMDB : (@LogicEMPB α) = LogicEMDB := by
  hilbert_eq_axioms

end LogicEMPB

end
