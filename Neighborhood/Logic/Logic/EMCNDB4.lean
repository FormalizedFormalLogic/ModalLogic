module

public import Neighborhood.Logic.Logic.EMCNTDB45

@[expose] public section

variable {α : Type u}

namespace LogicEMCNDB4

/-- The axioms `T`, `5` are redundant over `M`, `C`, `N`, `D`, `B`, `4`. -/
theorem eq_LogicEMCNTDB45 : (@LogicEMCNDB4 α) = LogicEMCNTDB45 := by
  hilbert_eq_axioms

instance : (@LogicEMCNDB4 α).IsConsistent := by
  rw [eq_LogicEMCNTDB45]; infer_instance

end LogicEMCNDB4

end
