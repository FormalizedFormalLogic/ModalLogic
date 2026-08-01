module

public import Neighborhood.Logic.Logic.ECT5

@[expose] public section

variable {α : Type u}

namespace LogicECNT45

/-- The axiom schemes `N` and `4` are redundant over `C`, `T` and `5`. -/
theorem eq_LogicECT5 : (@LogicECNT45 α) = LogicECT5 := by
  hilbert_eq_axioms

end LogicECNT45

end
