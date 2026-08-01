module

public import Neighborhood.Logic.Logic.ET4

@[expose] public section

variable {α : Type u}

namespace LogicETD4

/-- The axiom `D` is redundant over `T`. -/
theorem eq_LogicET4 : (@LogicETD4 α) = LogicET4 := by
  hilbert_eq_axioms

end LogicETD4

end
