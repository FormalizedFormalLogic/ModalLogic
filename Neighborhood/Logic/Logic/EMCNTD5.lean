module

public import Neighborhood.Logic.Logic.EMCNTDB45

@[expose] public section

variable {α : Type u}

namespace LogicEMCNTD5

/-- The axioms `B`, `4` are redundant over `M`, `C`, `N`, `T`, `D`, `5`. -/
theorem eq_LogicEMCNTDB45 : (@LogicEMCNTD5 α) = LogicEMCNTDB45 := by
  hilbert_eq_axioms

instance : (@LogicEMCNTD5 α).IsConsistent := by
  rw [eq_LogicEMCNTDB45]; infer_instance

end LogicEMCNTD5

end
