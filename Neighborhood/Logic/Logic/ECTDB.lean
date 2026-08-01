module

public import Neighborhood.Logic.Logic.ECTB

@[expose] public section

variable {α : Type u}

namespace LogicECTDB

/-- The axiom scheme `D` is redundant over `C`, `T` and `B`. -/
theorem eq_LogicECTB : (@LogicECTDB α) = LogicECTB := by
  hilbert_eq_axioms

end LogicECTDB

end
