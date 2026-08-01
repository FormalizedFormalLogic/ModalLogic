module

public import Neighborhood.Logic.Logic.EMCNTDB45

@[expose] public section

variable {α : Type u}

namespace LogicEMCNTB5

/-- The axioms `D`, `4` are redundant over `M`, `C`, `N`, `T`, `B`, `5`. -/
theorem eq_LogicEMCNTDB45 : (@LogicEMCNTB5 α) = LogicEMCNTDB45 := by
  hilbert_eq_axioms

instance : (@LogicEMCNTB5 α).IsConsistent := by
  rw [eq_LogicEMCNTDB45]; infer_instance

end LogicEMCNTB5

end
