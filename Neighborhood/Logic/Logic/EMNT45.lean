module

public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEMNT45

/-- Over `EMT5`, the axiom schemes `N` and `4` are redundant. -/
theorem eq_LogicEMT5 : (@LogicEMNT45 α) = LogicEMT5 := by
  hilbert_eq_axioms

end LogicEMNT45

end
