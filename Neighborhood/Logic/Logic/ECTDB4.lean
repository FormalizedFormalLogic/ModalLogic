module

public import Neighborhood.Logic.Logic.ECT5

@[expose] public section

variable {α : Type u}

namespace LogicECTDB4

/-- Over `C`, `T`, and `5`, the axiom schemes `D`, `B`, and `4` axiomatise the same logic. -/
theorem eq_LogicECT5 : (@LogicECTDB4 α) = LogicECT5 := by
  hilbert_eq_axioms

end LogicECTDB4

end
