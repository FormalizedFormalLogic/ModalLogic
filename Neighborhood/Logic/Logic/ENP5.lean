module

public import Neighborhood.Logic.Logic.EP5

@[expose] public section

variable {α : Type u}

namespace LogicENP5

/-- The axiom `N` is redundant over `P` and `5`. -/
theorem eq_LogicEP5 : (@LogicENP5 α) = LogicEP5 := by
  hilbert_eq_axioms

end LogicENP5

end
