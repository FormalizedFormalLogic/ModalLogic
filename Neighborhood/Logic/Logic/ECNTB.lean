module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

namespace LogicECNTB

/-- The axiom `N` is redundant over `T` and `B`. -/
theorem eq_LogicECTB : (@LogicECNTB α) = LogicECTB := by
  hilbert_eq_axioms

end LogicECNTB

end
