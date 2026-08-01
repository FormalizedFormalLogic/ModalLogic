module

public import Neighborhood.Logic.Logic.EMCNTDB45

@[expose] public section

variable {α : Type u}

namespace LogicEMCTDB4

/-- The axioms `N`, `5` are redundant over `M`, `C`, `T`, `D`, `B`, `4`. -/
theorem eq_LogicEMCNTDB45 : (@LogicEMCTDB4 α) = LogicEMCNTDB45 := by
  hilbert_eq_axioms

instance : (@LogicEMCTDB4 α).IsConsistent := by
  rw [eq_LogicEMCNTDB45]; infer_instance

end LogicEMCTDB4

end
