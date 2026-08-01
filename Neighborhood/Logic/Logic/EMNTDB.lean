module

public import Neighborhood.Logic.Logic.EMTB

@[expose] public section

variable {α : Type u}

namespace LogicEMNTDB

/-- Over `EMTB`, the axiom schemes `N` and `D` are redundant. -/
theorem eq_LogicEMTB : (@LogicEMNTDB α) = LogicEMTB := by
  hilbert_eq_axioms

end LogicEMNTDB

end
