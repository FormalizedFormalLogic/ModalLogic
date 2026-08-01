module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

namespace LogicEMCNB

/-- The axiom scheme `C` and the axiom `N` are both redundant over `M` and `B`. -/
theorem eq_LogicEMB : (@LogicEMCNB α) = LogicEMB := by
  hilbert_eq_axioms

end LogicEMCNB

end
