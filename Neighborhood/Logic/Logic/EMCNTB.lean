module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

namespace LogicEMCNTB

/-- The axiom scheme `C` is redundant over `M`, `T`, and `B`, and the axiom `N` is redundant
over `T` and `B`. -/
theorem eq_LogicEMTB : (@LogicEMCNTB α) = LogicEMTB := by
  hilbert_eq_axioms

end LogicEMCNTB

end
