module

public import Neighborhood.Logic.Logic.EMTB

@[expose] public section

variable {α : Type u}

namespace LogicEMCTDB

/-- The axiom schemes `C` and `D` are redundant over `M`, `T`, and `B`. -/
theorem eq_LogicEMTB : (@LogicEMCTDB α) = LogicEMTB := by
  hilbert_eq_axioms

end LogicEMCTDB

end
