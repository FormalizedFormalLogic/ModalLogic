module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

namespace LogicEMCB4

/-- The axiom scheme `C` is redundant over `M`, `B`, and `4`. -/
theorem eq_LogicEMB4 : (@LogicEMCB4 α) = LogicEMB4 := by
  hilbert_eq_axioms

end LogicEMCB4

end
