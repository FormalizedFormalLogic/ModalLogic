module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

namespace LogicEMND5

/-- The axiom `N` is redundant over `M` and `5`. -/
theorem eq_LogicEMD5 : (@LogicEMND5 α) = LogicEMD5 := by
  hilbert_eq_axioms

end LogicEMND5

end
