module

public import Neighborhood.Logic.Logic.EMCNTDB45

@[expose] public section

variable {α : Type u}

namespace LogicEMCTDB5

/-- The axioms `N`, `4` are redundant over `M`, `C`, `T`, `D`, `B`, `5`. -/
theorem eq_LogicEMCNTDB45 : (@LogicEMCTDB5 α) = LogicEMCNTDB45 := by
  hilbert_eq_axioms

instance : (@LogicEMCTDB5 α).IsConsistent := by
  rw [eq_LogicEMCNTDB45]; infer_instance

end LogicEMCTDB5

end
