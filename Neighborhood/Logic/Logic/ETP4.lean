module

public import Neighborhood.Logic.Logic.ET4

@[expose] public section

variable {α : Type u}

namespace LogicETP4

/-- The axiom `P` is redundant over `T`. -/
theorem eq_LogicET4 : (@LogicETP4 α) = LogicET4 := by
  hilbert_eq_axioms

end LogicETP4

end
