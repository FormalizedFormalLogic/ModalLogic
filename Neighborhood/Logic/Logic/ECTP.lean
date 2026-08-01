module

public import Neighborhood.Logic.Logic.ECT

@[expose] public section

variable {α : Type u}

namespace LogicECTP

/-- The axiom `P` is redundant over `C` and `T`. -/
theorem eq_LogicECT : (@LogicECTP α) = LogicECT := by
  hilbert_eq_axioms

end LogicECTP

end
