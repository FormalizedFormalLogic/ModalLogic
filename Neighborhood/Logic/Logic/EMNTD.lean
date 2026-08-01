module

public import Neighborhood.Logic.Logic.EMNT

@[expose] public section

variable {α : Type u}

namespace LogicEMNTD

/-- The axiom scheme `D` is redundant over `M`, `N` and `T`. -/
theorem eq_LogicEMNT : (@LogicEMNTD α) = LogicEMNT := by
  hilbert_eq_axioms

end LogicEMNTD

end
