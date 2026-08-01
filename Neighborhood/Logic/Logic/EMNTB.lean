module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

namespace LogicEMNTB

/-- The axiom `N` is redundant over `T` and `B`. -/
theorem eq_LogicEMTB : (@LogicEMNTB α) = LogicEMTB := by
  hilbert_eq_axioms

end LogicEMNTB

end
