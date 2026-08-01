module

public import Neighborhood.Logic.Logic.EMCNTDB45

@[expose] public section

variable {α : Type u}

namespace LogicEMNTD45

/-- The axioms `C`, `B` are redundant over `M`, `N`, `T`, `D`, `4`, `5`. -/
theorem eq_LogicEMCNTDB45 : (@LogicEMNTD45 α) = LogicEMCNTDB45 := by
  hilbert_eq_axioms

instance : (@LogicEMNTD45 α).IsConsistent := by
  rw [eq_LogicEMCNTDB45]; infer_instance

end LogicEMNTD45

end
