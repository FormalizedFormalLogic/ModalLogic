module

public import Neighborhood.Logic.Logic.ETB

@[expose] public section

variable {α : Type u}

namespace LogicETPB

/-- The axiom `P` is redundant over `T`. -/
theorem eq_LogicETB : (@LogicETPB α) = LogicETB := by
  hilbert_eq_axioms

end LogicETPB

end
