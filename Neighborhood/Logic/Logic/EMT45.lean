module

public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEMT45

/-- The axiom scheme `4` is redundant over `M`, `T` and `5`. -/
theorem eq_LogicEMT5 : (@LogicEMT45 α) = LogicEMT5 := by
  hilbert_eq_axioms

end LogicEMT45

end
