module

public import Neighborhood.Logic.Logic.END

@[expose] public section

variable {α : Type u}

namespace LogicENDP

/-- The axiom `P` is redundant over `N` and `D`. -/
theorem eq_LogicEND : (@LogicENDP α) = LogicEND := by
  hilbert_eq_axioms

end LogicENDP

end
