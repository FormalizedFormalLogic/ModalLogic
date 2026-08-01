module

public import Neighborhood.Logic.Logic.EMTB

@[expose] public section

variable {α : Type u}

namespace LogicEKTB

/-- `EKTB` and `EMTB` axiomatise the same logic: `M` is derivable from `K`, `T` and `B`, while
conversely `K` is derivable from `M`, `T` and `B`. -/
theorem eq_LogicEMTB : (@LogicEKTB α) = LogicEMTB := by
  hilbert_eq_axioms

end LogicEKTB

end
