module

public import Neighborhood.Logic.Logic.EMCNTDB45

@[expose] public section

variable {α : Type u}

namespace LogicEMCNTD45

/-- The axiom `B` is redundant over `M`, `C`, `N`, `T`, `D`, `4`, `5`. -/
theorem eq_LogicEMCNTDB45 : (@LogicEMCNTD45 α) = LogicEMCNTDB45 := by
  hilbert_eq_axioms

instance : (@LogicEMCNTD45 α).IsConsistent := by
  rw [eq_LogicEMCNTDB45]; infer_instance

end LogicEMCNTD45

end
