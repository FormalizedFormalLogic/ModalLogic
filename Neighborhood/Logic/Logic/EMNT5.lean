module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

namespace LogicEMNT5

/-- The axiom `N` is redundant over `M`, `T`, and `5`. -/
theorem eq_LogicEMT5 : (@LogicEMNT5 α) = LogicEMT5 := by
  hilbert_eq_axioms

end LogicEMNT5

end
