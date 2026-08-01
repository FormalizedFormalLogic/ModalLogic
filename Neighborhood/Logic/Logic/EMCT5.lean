module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

namespace LogicEMCT5

/-- The axiom scheme `C` is redundant over `M`, `T`, and `5`. -/
theorem eq_LogicEMT5 : (@LogicEMCT5 α) = LogicEMT5 := by
  hilbert_eq_axioms

end LogicEMCT5

end
