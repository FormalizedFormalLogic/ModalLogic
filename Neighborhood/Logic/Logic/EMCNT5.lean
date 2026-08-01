module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

namespace LogicEMCNT5

/-- The axiom scheme `C` and the axiom `N` are redundant over `M`, `T`, and `5`. -/
theorem eq_LogicEMT5 : (@LogicEMCNT5 α) = LogicEMT5 := by
  hilbert_eq_axioms

end LogicEMCNT5

end
