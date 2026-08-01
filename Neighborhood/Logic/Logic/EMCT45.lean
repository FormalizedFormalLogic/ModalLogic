module

public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEMCT45

/-- The axiom schemes `C` and `Four` are redundant over `M`, `T`, and `Five`. -/
theorem eq_LogicEMT5 : (@LogicEMCT45 α) = LogicEMT5 := by
  hilbert_eq_axioms

end LogicEMCT45

end
