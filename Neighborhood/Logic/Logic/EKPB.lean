module

public import Neighborhood.Logic.Logic.EMDB

@[expose] public section

variable {α : Type u}

namespace LogicEKPB

/-- `EKPB` and `EMDB` axiomatise the same logic: `M` and `D` are derivable from `K`, `P` and `B`,
while conversely `K` and `P` are derivable from `M`, `D` and `B`. -/
theorem eq_LogicEMDB : (@LogicEKPB α) = LogicEMDB := by
  hilbert_eq_axioms

end LogicEKPB

end
