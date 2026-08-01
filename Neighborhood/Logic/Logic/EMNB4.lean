module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

namespace LogicEMNB4

/-- The axiom `N` is redundant over `M`, `B`, and `4`. -/
theorem eq_LogicEMB4 : (@LogicEMNB4 α) = LogicEMB4 := by
  hilbert_eq_axioms

end LogicEMNB4

end
