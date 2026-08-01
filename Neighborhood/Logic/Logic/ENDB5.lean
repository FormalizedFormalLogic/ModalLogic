module

public import Neighborhood.Logic.Logic.EDB5

@[expose] public section

variable {α : Type u}

namespace LogicENDB5

/-- The axiom scheme `N` is redundant over `D`, `B`, and `5`. -/
theorem eq_LogicEDB5 : (@LogicENDB5 α) = LogicEDB5 := by
  hilbert_eq_axioms

end LogicENDB5

end
