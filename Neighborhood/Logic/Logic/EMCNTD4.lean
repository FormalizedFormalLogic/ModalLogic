module

public import Neighborhood.Logic.Logic.EMCNT4

@[expose] public section

variable {α : Type u}

namespace LogicEMCNTD4

/-- The axiom `D` is redundant over `M`, `C`, `N`, `T`, `4`. -/
theorem eq_LogicEMCNT4 : (@LogicEMCNTD4 α) = LogicEMCNT4 := by
  hilbert_eq_axioms

instance : (@LogicEMCNTD4 α).IsConsistent := by
  rw [eq_LogicEMCNT4]; infer_instance

end LogicEMCNTD4

end
