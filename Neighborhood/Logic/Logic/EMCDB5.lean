module

public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEMCDB5

/-- Over `M`, `T`, and `5`, the axiom schemes `C`, `D`, and `B` axiomatise the same logic. -/
theorem eq_LogicEMT5 : (@LogicEMCDB5 α) = LogicEMT5 := by
  hilbert_eq_axioms

end LogicEMCDB5

end
