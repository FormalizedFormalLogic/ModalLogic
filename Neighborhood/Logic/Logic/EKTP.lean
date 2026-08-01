module

public import Neighborhood.Logic.Logic.EKT

@[expose] public section

variable {α : Type u}

namespace LogicEKTP

/-- The axiom `P` is redundant over `K` and `T`. -/
theorem eq_LogicEKT : (@LogicEKTP α) = LogicEKT := by
  hilbert_eq_axioms

end LogicEKTP

end
