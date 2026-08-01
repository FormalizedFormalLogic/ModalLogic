module

public import Neighborhood.Logic.Logic.ET5

@[expose] public section

variable {α : Type u}

namespace LogicETD5

/-- The axiom `D` is redundant over `T`. -/
theorem eq_LogicET5 : (@LogicETD5 α) = LogicET5 := by
  hilbert_eq_axioms

end LogicETD5

end
