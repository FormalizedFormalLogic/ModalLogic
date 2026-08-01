module

public import Neighborhood.Logic.Logic.ENT

@[expose] public section

variable {α : Type u}

namespace LogicENTP

/-- The axiom `P` is redundant over `N` and `T`. -/
theorem eq_LogicENT : (@LogicENTP α) = LogicENT := by
  hilbert_eq_axioms

end LogicENTP

end
