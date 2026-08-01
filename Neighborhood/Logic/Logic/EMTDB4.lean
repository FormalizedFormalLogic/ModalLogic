module

public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEMTDB4

/-- The axiom schemes `D` and `B` are redundant over `M`, `T` and `4`, which axiomatises the same logic as `M`, `T` and `5`. -/
theorem eq_LogicEMT5 : (@LogicEMTDB4 α) = LogicEMT5 := by
  hilbert_eq_axioms

end LogicEMTDB4

end
