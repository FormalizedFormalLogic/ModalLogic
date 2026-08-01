module

public import Neighborhood.Logic.Logic.ET5

@[expose] public section

variable {α : Type u}

namespace LogicETD45

/-- Over `T`, the axiom schemes `D`, `4`, and `5` axiomatise the same logic as `5`. -/
theorem eq_LogicET5 : (@LogicETD45 α) = LogicET5 := by
  hilbert_eq_axioms

end LogicETD45

end
