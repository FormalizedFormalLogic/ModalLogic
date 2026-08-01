module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

namespace LogicEMCDB

/-- The axiom scheme `C` is redundant over `M`, `D`, and `B`. -/
theorem eq_LogicEMDB : (@LogicEMCDB α) = LogicEMDB := by
  hilbert_eq_axioms

end LogicEMCDB

end
