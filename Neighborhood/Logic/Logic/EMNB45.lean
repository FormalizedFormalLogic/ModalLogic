module

public import Neighborhood.Logic.Logic.EMB4

@[expose] public section

variable {α : Type u}

namespace LogicEMNB45

/-- The axiom scheme `N` and the axiom scheme `5` are redundant over `M`, `B`, and `4`. -/
theorem eq_LogicEMB4 : (@LogicEMNB45 α) = LogicEMB4 := by
  hilbert_eq_axioms

end LogicEMNB45

end
