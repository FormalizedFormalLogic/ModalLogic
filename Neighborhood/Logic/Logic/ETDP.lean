module

public import Neighborhood.Logic.Logic.ET

@[expose] public section

variable {α : Type u}

namespace LogicETDP

/-- The axioms `D` and `P` are redundant over `T`. -/
theorem eq_LogicET : (@LogicETDP α) = LogicET := by
  hilbert_eq_axioms

end LogicETDP

end
