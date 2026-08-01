module

public import Neighborhood.Logic.Logic.ET5

@[expose] public section

variable {α : Type u}

namespace LogicENTB5

/-- The axiom `N` and the axiom scheme `B` are redundant over `T` and `5`. -/
theorem eq_LogicET5 : (@LogicENTB5 α) = LogicET5 := by
  hilbert_eq_axioms

end LogicENTB5

end
