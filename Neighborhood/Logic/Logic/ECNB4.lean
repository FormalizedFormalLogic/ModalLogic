module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

namespace LogicECNB4

/-- The axiom `N` is redundant over `B` and `4`. -/
theorem eq_LogicECB4 : (@LogicECNB4 α) = LogicECB4 := by
  hilbert_eq_axioms

end LogicECNB4

end
