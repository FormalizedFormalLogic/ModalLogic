module

public import Neighborhood.Logic.Logic.EKT

@[expose] public section

variable {α : Type u}

namespace LogicEKTD

/-- The axiom `D` is redundant over `K` and `T`. -/
theorem eq_LogicEKT : (@LogicEKTD α) = LogicEKT := by
  hilbert_eq_axioms

end LogicEKTD

end
