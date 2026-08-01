module

public import Neighborhood.Logic.Logic.ET5

@[expose] public section

variable {α : Type u}

namespace LogicENTB45

/-- The axiom schemes `N`, `B`, and `Four` are redundant over `T` and `Five`. -/
theorem eq_LogicET5 : (@LogicENTB45 α) = LogicET5 := by
  hilbert_eq_axioms

end LogicENTB45

end
