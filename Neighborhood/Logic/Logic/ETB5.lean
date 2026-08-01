module

public import Neighborhood.Logic.Logic.ET5

@[expose] public section

variable {α : Type u}

namespace LogicETB5

/-- The axiom `B` is redundant over `T` and `5`. -/
theorem eq_LogicET5 : (@LogicETB5 α) = LogicET5 := by
  hilbert_eq_axioms

end LogicETB5

end
