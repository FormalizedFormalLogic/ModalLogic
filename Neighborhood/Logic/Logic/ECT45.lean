module

public import Neighborhood.Logic.Logic.ECT5

@[expose] public section

variable {α : Type u}

namespace LogicECT45

/-- The axiom scheme `4` is redundant over `C`, `T`, and `5`. -/
theorem eq_LogicECT5 : (@LogicECT45 α) = LogicECT5 := by
  hilbert_eq_axioms

end LogicECT45

end
