module

public import Neighborhood.Logic.Logic.EMCNTDB45

@[expose] public section

variable {α : Type u}

namespace LogicEMCTD45

/-- The axioms `N`, `B` are redundant over `M`, `C`, `T`, `D`, `4`, `5`. -/
theorem eq_LogicEMCNTDB45 : (@LogicEMCTD45 α) = LogicEMCNTDB45 := by
  hilbert_eq_axioms

instance : (@LogicEMCTD45 α).IsConsistent := by
  rw [eq_LogicEMCNTDB45]; infer_instance

end LogicEMCTD45

end
