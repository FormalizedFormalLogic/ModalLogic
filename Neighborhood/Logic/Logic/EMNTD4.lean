module

public import Neighborhood.Logic.Logic.EMNT4

@[expose] public section

variable {α : Type u}

namespace LogicEMNTD4

/-- The axiom scheme `D` is redundant over `M`, `N`, `T`, and `Four`. -/
theorem eq_LogicEMNT4 : (@LogicEMNTD4 α) = LogicEMNT4 := by
  hilbert_eq_axioms

end LogicEMNTD4

end
