module

public import Neighborhood.Logic.Logic.EMB4

@[expose] public section

variable {α : Type u}

namespace LogicEMCNB5

/-- Over `EMB4`, the axiom schemes `C` and `N` are redundant. -/
theorem eq_LogicEMB4 : (@LogicEMCNB5 α) = LogicEMB4 := by
  hilbert_eq_axioms

end LogicEMCNB5

end
