module

public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEMTD45

/-- The axiom schemes `D` and `Four` are redundant over `M`, `T`, and `Five`. -/
theorem eq_LogicEMT5 : (@LogicEMTD45 α) = LogicEMT5 := by
  hilbert_eq_axioms

end LogicEMTD45

end
