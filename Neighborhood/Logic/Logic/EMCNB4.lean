module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

namespace LogicEMCNB4

/-- The axiom scheme `C` and the axiom `N` are both redundant over `M`, `B`, and `4`. -/
theorem eq_LogicEMB4 : (@LogicEMCNB4 α) = LogicEMB4 := by
  hilbert_eq_axioms

end LogicEMCNB4

end
