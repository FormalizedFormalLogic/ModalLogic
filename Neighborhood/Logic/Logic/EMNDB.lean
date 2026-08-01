module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

namespace LogicEMNDB

/-- The axiom `N` is redundant over `M`, `D`, and `B`. -/
theorem eq_LogicEMDB : (@LogicEMNDB α) = LogicEMDB := by
  hilbert_eq_axioms

end LogicEMNDB

end
