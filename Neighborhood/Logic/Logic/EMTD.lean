module

public import Neighborhood.Logic.Logic.EMT

@[expose] public section

variable {α : Type u}

namespace LogicEMTD

/-- The axiom scheme `D` is redundant over `M` and `T`. -/
theorem eq_LogicEMT : (@LogicEMTD α) = LogicEMT := by
  hilbert_eq_axioms

end LogicEMTD

end
