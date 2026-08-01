module

public import Neighborhood.Logic.Logic.EMT

@[expose] public section

variable {α : Type u}

namespace LogicEMTP

/-- The axiom `P` is redundant over `M` and `T`. -/
theorem eq_LogicEMT : (@LogicEMTP α) = LogicEMT := by
  hilbert_eq_axioms

end LogicEMTP

end
