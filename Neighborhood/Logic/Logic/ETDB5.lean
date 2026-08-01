module

public import Neighborhood.Logic.Logic.ET5

@[expose] public section

variable {α : Type u}

namespace LogicETDB5

/-- The axiom schemes `D` and `B` are redundant over `T` and `5`. -/
theorem eq_LogicET5 : (@LogicETDB5 α) = LogicET5 := by
  hilbert_eq_axioms

end LogicETDB5

end
