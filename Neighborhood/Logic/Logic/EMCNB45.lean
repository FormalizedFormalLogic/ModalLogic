module

public import Neighborhood.Logic.Logic.EMB4

@[expose] public section

variable {α : Type u}

namespace LogicEMCNB45

/-- The axioms `C`, `N`, `5` are redundant over `M`, `B`, `4`. -/
theorem eq_LogicEMB4 : (@LogicEMCNB45 α) = LogicEMB4 := by
  hilbert_eq_axioms

instance : (@LogicEMCNB45 α).IsConsistent := by
  rw [eq_LogicEMB4]; infer_instance

end LogicEMCNB45

end
