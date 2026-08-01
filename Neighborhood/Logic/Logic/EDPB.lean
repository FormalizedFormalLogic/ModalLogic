module

public import Neighborhood.Logic.Logic.ENDB

@[expose] public section

variable {α : Type u}

namespace LogicEDPB

/-- `EDPB` and `ENDB` axiomatise the same logic: `P` is derivable from `D` and `N`, while
conversely `N` is derivable from `P` and `B`. -/
theorem eq_LogicENDB : (@LogicEDPB α) = LogicENDB := by
  hilbert_eq_axioms

end LogicEDPB

end
