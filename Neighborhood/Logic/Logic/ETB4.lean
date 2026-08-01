module

public import Neighborhood.Logic.Logic.ET5

@[expose] public section

variable {α : Type u}

namespace LogicETB4

/-- Over `E`, the axioms `T`, `B`, and `4` derive `5`, and conversely `T` and `5` derive
`B` and `4`. -/
theorem eq_LogicET5 : (@LogicETB4 α) = LogicET5 := by
  hilbert_eq_axioms

end LogicETB4

end
