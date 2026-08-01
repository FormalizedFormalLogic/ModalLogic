module

public import Neighborhood.Logic.Logic.EMT4

@[expose] public section

variable {α : Type u}

namespace LogicEMTD4

/-- The axiom scheme `D` is redundant over `M`, `T` and `4`. -/
theorem eq_LogicEMT4 : (@LogicEMTD4 α) = LogicEMT4 := by
  hilbert_eq_axioms

end LogicEMTD4

end
