module

public import Neighborhood.Logic.Logic.ET5

@[expose] public section

variable {α : Type u}

namespace LogicETDB45

/-- The axiom scheme `D` and the axiom scheme `B` are redundant over `T` and `5`. -/
theorem eq_LogicET5 : (@LogicETDB45 α) = LogicET5 := by
  hilbert_eq_axioms

end LogicETDB45

end
