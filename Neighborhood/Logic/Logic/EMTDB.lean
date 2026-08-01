module

public import Neighborhood.Logic.Logic.EMTB

@[expose] public section

variable {α : Type u}

namespace LogicEMTDB

/-- The axiom scheme `D` is redundant over `M`, `T`, and `B`. -/
theorem eq_LogicEMTB : (@LogicEMTDB α) = LogicEMTB := by
  hilbert_eq_axioms

end LogicEMTDB

end
