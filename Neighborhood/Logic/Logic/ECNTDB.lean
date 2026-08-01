module

public import Neighborhood.Logic.Logic.ECTB

@[expose] public section

variable {α : Type u}

namespace LogicECNTDB

/-- The axiom schemes `N` and `D` are redundant over `C`, `T` and `B`. -/
theorem eq_LogicECTB : (@LogicECNTDB α) = LogicECTB := by
  hilbert_eq_axioms

end LogicECNTDB

end
