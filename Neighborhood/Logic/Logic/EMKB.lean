module

public import Neighborhood.Logic.Logic.EMB

@[expose] public section

variable {α : Type u}

namespace LogicEMKB

/-- The axiom scheme `K` is redundant over `M` and `B`. -/
theorem eq_LogicEMB : (@LogicEMKB α) = LogicEMB := by
  hilbert_eq_axioms

end LogicEMKB

end
