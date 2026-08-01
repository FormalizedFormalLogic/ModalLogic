module

public import Neighborhood.Logic.Logic.ECNT

@[expose] public section

variable {α : Type u}

namespace LogicECNTD

/-- The axiom scheme `D` is redundant over `C`, `N` and `T`. -/
theorem eq_LogicECNT : (@LogicECNTD α) = LogicECNT := by
  hilbert_eq_axioms

end LogicECNTD

end
