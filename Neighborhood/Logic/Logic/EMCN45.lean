module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

namespace LogicEMCN45

/-- The axiom `N` is redundant over `M`, `C`, `4`, and `5`. -/
theorem eq_LogicEMC45 : (@LogicEMCN45 α) = LogicEMC45 := by
  hilbert_eq_axioms

end LogicEMCN45

end
