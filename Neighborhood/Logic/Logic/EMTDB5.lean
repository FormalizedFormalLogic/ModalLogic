module

public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEMTDB5

/-- Over `EMT5`, the axiom schemes `D` and `B` are redundant. -/
theorem eq_LogicEMT5 : (@LogicEMTDB5 α) = LogicEMT5 := by
  hilbert_eq_axioms

end LogicEMTDB5

end
