module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

namespace LogicEMND45

/-- The axiom `N` is redundant over `M`, `4`, and `5`. -/
theorem eq_LogicEMD45 : (@LogicEMND45 α) = LogicEMD45 := by
  hilbert_eq_axioms

end LogicEMND45

end
