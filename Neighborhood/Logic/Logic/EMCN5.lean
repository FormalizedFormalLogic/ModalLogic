module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

namespace LogicEMCN5

/-- The axiom `N` is redundant over `M`, `C` and `5`. -/
theorem eq_LogicEMC5 : (@LogicEMCN5 α) = LogicEMC5 := by
  hilbert_eq_axioms

end LogicEMCN5

end
