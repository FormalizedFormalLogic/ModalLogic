module

public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEMDB45

/-- Over `M`, `T`, and `5`, the axiom schemes `D`, `B`, and `4` axiomatise the same logic. -/
theorem eq_LogicEMT5 : (@LogicEMDB45 α) = LogicEMT5 := by
  hilbert_eq_axioms

end LogicEMDB45

end
