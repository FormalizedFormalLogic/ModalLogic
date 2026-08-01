module

public import Neighborhood.Logic.Logic.EMCNTDB45

@[expose] public section

variable {α : Type u}

namespace LogicEMNTDB4

/-- The axioms `C`, `5` are redundant over `M`, `N`, `T`, `D`, `B`, `4`. -/
theorem eq_LogicEMCNTDB45 : (@LogicEMNTDB4 α) = LogicEMCNTDB45 := by
  hilbert_eq_axioms

instance : (@LogicEMNTDB4 α).IsConsistent := by
  rw [eq_LogicEMCNTDB45]; infer_instance

end LogicEMNTDB4

end
