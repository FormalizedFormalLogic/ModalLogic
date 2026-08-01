module

public import Neighborhood.Logic.Logic.EMC5

@[expose] public section

variable {α : Type u}

namespace LogicENK5

/-- `ENK5` and `EMC5` axiomatise the same logic: `M` and `C` are derivable from `K`, `N` and
`5`, while conversely `K` and `N` are derivable from `M`, `C` and `5`. -/
theorem eq_LogicEMC5 : (@LogicENK5 α) = LogicEMC5 := by
  hilbert_eq_axioms

end LogicENK5

end
