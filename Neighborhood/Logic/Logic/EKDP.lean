module

public import Neighborhood.Logic.Logic.EKP

@[expose] public section

variable {α : Type u}

namespace LogicEKDP

/-- The axiom `D` is redundant over `K` and `P`. -/
theorem eq_LogicEKP : (@LogicEKDP α) = LogicEKP := by
  hilbert_eq_axioms

end LogicEKDP

end
