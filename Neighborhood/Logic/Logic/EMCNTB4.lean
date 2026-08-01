module

public import Neighborhood.Logic.Logic.EMCNTDB45

@[expose] public section

variable {α : Type u}

namespace LogicEMCNTB4

/-- The axioms `D`, `5` are redundant over `M`, `C`, `N`, `T`, `B`, `4`. -/
theorem eq_LogicEMCNTDB45 : (@LogicEMCNTB4 α) = LogicEMCNTDB45 := by
  hilbert_eq_axioms

instance : (@LogicEMCNTB4 α).IsConsistent := by
  rw [eq_LogicEMCNTDB45]; infer_instance

end LogicEMCNTB4

end
