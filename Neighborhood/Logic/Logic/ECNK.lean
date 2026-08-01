module

public import Neighborhood.Logic.Logic.EMCN

@[expose] public section

variable {α : Type u}

namespace LogicECNK

/-- `ECNK` and `EMCN` axiomatise the same logic: `M` is derivable from `K` and `N`, while
conversely `K` is derivable from `M` and `C`. -/
theorem eq_LogicEMCN : (@LogicECNK α) = LogicEMCN := by
  hilbert_eq_axioms

end LogicECNK

end
