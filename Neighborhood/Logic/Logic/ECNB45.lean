module

public import Neighborhood.Logic.Logic.ECB45

@[expose] public section

variable {α : Type u}

namespace LogicECNB45

/-- The axiom scheme `N` is redundant over `C`, `B`, `4` and `5`. -/
theorem eq_LogicECB45 : (@LogicECNB45 α) = LogicECB45 := by
  hilbert_eq_axioms

end LogicECNB45

end
