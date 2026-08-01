module

public import Neighborhood.Logic.Logic.EMCNTDB45

@[expose] public section

variable {α : Type u}

namespace LogicEMCNDB5

/-- The axioms `T`, `4` are redundant over `M`, `C`, `N`, `D`, `B`, `5`. -/
theorem eq_LogicEMCNTDB45 : (@LogicEMCNDB5 α) = LogicEMCNTDB45 := by
  hilbert_eq_axioms

instance : (@LogicEMCNDB5 α).IsConsistent := by
  rw [eq_LogicEMCNTDB45]; infer_instance

end LogicEMCNDB5

end
