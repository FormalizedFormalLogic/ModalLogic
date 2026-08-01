module

public import Neighborhood.Logic.Logic.ET5

@[expose] public section

variable {α : Type u}

namespace LogicETP5

/-- The axiom `P` is redundant over `T`. -/
theorem eq_LogicET5 : (@LogicETP5 α) = LogicET5 := by
  hilbert_eq_axioms

end LogicETP5

end
