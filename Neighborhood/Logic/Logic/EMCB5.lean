module

public import Neighborhood.Logic.Logic.EMB4

@[expose] public section

variable {α : Type u}

namespace LogicEMCB5

/-- The axiom scheme `C` is redundant over `M`, `B` and `5`, and the axiom scheme `4` is derivable
over `M`, `C`, `B` and `5`. -/
theorem eq_LogicEMB4 : (@LogicEMCB5 α) = LogicEMB4 := by
  hilbert_eq_axioms

end LogicEMCB5

end
