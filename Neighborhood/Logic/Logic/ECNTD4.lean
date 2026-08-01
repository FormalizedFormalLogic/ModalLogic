module

public import Neighborhood.Logic.Logic.ECNT4

@[expose] public section

variable {α : Type u}

namespace LogicECNTD4

/-- The axiom scheme `D` is redundant over `C`, `N`, `T`, and `4`. -/
theorem eq_LogicECNT4 : (@LogicECNTD4 α) = LogicECNT4 := by
  hilbert_eq_axioms

end LogicECNTD4

end
