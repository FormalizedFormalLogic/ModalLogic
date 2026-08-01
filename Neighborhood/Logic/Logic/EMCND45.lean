module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

namespace LogicEMCND45

/-- The axiom `N` is redundant over `M`, `C`, `4`, and `5`. -/
theorem eq_LogicEMCD45 : (@LogicEMCND45 α) = LogicEMCD45 := by
  hilbert_eq_axioms

end LogicEMCND45

end
