module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

namespace LogicECNT5

/-- The axiom `N` is redundant over `T` and `5`. -/
theorem eq_LogicECT5 : (@LogicECNT5 α) = LogicECT5 := by
  hilbert_eq_axioms

end LogicECNT5

end
