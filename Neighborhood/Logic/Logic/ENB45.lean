module

public import Neighborhood.Logic.Logic.EB45

@[expose] public section

variable {α : Type u}

namespace LogicENB45

/-- The axiom `N` is redundant over `B`, `4` and `5`. -/
theorem eq_LogicEB45 : (@LogicENB45 α) = LogicEB45 := by
  hilbert_eq_axioms

end LogicENB45

end
