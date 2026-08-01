module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

namespace LogicEMCTB

/-- The axiom scheme `C` is redundant over `M`, `T`, and `B`. -/
theorem eq_LogicEMTB : (@LogicEMCTB α) = LogicEMTB := by
  hilbert_eq_axioms

end LogicEMCTB

end
