module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

namespace LogicEMN45

/-- The axiom `N` is redundant over `M`, `4` and `5`. -/
theorem eq_LogicEM45 : (@LogicEMN45 α) = LogicEM45 := by
  hilbert_eq_axioms

end LogicEMN45

end
