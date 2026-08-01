module

public import Neighborhood.Logic.Logic.ET5

@[expose] public section

variable {α : Type u}

namespace LogicEDB45

/-- The axiom schemes `D`, `B`, `4` and `5` axiomatise the same logic as `T` and `5`. -/
theorem eq_LogicET5 : (@LogicEDB45 α) = LogicET5 := by
  hilbert_eq_axioms

end LogicEDB45

end
