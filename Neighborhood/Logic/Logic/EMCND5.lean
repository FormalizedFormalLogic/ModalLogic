module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

namespace LogicEMCND5

/-- The axiom `N` is redundant over `M`, `C`, and `5`. -/
theorem eq_LogicEMCD5 : (@LogicEMCND5 α) = LogicEMCD5 := by
  hilbert_eq_axioms

end LogicEMCND5

end
