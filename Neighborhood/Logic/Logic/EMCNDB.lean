module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

namespace LogicEMCNDB

/-- The axiom scheme `C` and the axiom `N` are both redundant over `M`, `D`, and `B`. -/
theorem eq_LogicEMDB : (@LogicEMCNDB α) = LogicEMDB := by
  hilbert_eq_axioms

end LogicEMCNDB

end
