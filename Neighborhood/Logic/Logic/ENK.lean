module

public import Neighborhood.Logic.Logic.EMCN

@[expose] public section

variable {α : Type u}

namespace LogicENK

/-- The axiom schemes `M` and `C` are both derivable from `N` and the axiom scheme `K`. -/
theorem eq_LogicEMCN : (@LogicENK α) = LogicEMCN := by
  hilbert_eq_axioms

end LogicENK

end
