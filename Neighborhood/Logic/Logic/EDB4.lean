module

public import Neighborhood.Logic.Logic.ET5

@[expose] public section

variable {α : Type u}

namespace LogicEDB4

/-- Over `E`, the axioms `D`, `B`, and `4` derive `T` and `5`, and conversely `T` and `5`
derive `D`, `B`, and `4`. -/
theorem eq_LogicET5 : (@LogicEDB4 α) = LogicET5 := by
  hilbert_eq_axioms

end LogicEDB4

end
