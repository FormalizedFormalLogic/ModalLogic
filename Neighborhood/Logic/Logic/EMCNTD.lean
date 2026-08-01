module

public import Neighborhood.Logic.Logic.ENKT

@[expose] public section

variable {α : Type u}

namespace LogicEMCNTD

/-- The axiom schemes `M` and `C` are redundant over `N`, `K` and `T`. -/
theorem eq_LogicENKT : (@LogicEMCNTD α) = LogicENKT := by
  hilbert_eq_axioms

end LogicEMCNTD

end
