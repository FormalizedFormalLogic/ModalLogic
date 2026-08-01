module

public import Neighborhood.Logic.Logic.ET5

@[expose] public section

variable {α : Type u}

namespace LogicETB45

/-- The axiom scheme `B` and the axiom scheme `4` are redundant over `T` and `5`. -/
theorem eq_LogicET5 : (@LogicETB45 α) = LogicET5 := by
  hilbert_eq_axioms

end LogicETB45

end
