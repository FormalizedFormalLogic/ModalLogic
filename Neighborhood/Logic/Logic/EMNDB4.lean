module

public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEMNDB4

/-- Over `M`, the axiom schemes `N`, `D`, `B`, and `Four` axiomatise the same logic as `T` and `Five`. -/
theorem eq_LogicEMT5 : (@LogicEMNDB4 α) = LogicEMT5 := by
  hilbert_eq_axioms

end LogicEMNDB4

end
