module

public import Neighborhood.Logic.Logic.EMCN

@[expose] public section

variable {α : Type u}

namespace LogicEMNK

/-- The axiom scheme `C` is derivable from `M`, `N` and the axiom scheme `K`. -/
theorem eq_LogicEMCN : (@LogicEMNK α) = LogicEMCN := by
  hilbert_eq_axioms

end LogicEMNK

end
