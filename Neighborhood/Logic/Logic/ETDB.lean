module

public import Neighborhood.Logic.Logic.ETB

@[expose] public section

variable {α : Type u}

namespace LogicETDB

/-- The axiom `D` is redundant over `T` and `B`. -/
theorem eq_LogicETB : (@LogicETDB α) = LogicETB := by
  hilbert_eq_axioms

end LogicETDB

end
