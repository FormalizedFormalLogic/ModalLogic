module

public import Neighborhood.Logic.Logic.ETB

@[expose] public section

variable {α : Type u}

namespace LogicENTDB

/-- The axiom `N` and the axiom scheme `D` are redundant over `T` and `B`. -/
theorem eq_LogicETB : (@LogicENTDB α) = LogicETB := by
  hilbert_eq_axioms

end LogicENTDB

end
