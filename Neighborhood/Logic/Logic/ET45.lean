module

public import Neighborhood.Logic.Logic.ET5

@[expose] public section

variable {α : Type u}

namespace LogicET45

/-- The axiom `4` is redundant over `T` and `5`. -/
theorem eq_LogicET5 : (@LogicET45 α) = LogicET5 := by
  hilbert_eq_axioms

end LogicET45

end
