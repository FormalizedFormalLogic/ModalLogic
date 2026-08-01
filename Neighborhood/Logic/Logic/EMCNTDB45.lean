module

public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEMCNTDB45

/-- The axioms `C`, `N`, `D`, `B`, `4` are redundant over `M`, `T`, `5`. -/
theorem eq_LogicEMT5 : (@LogicEMCNTDB45 α) = LogicEMT5 := by
  hilbert_eq_axioms

instance : (@LogicEMCNTDB45 α).IsConsistent := by
  rw [eq_LogicEMT5]; infer_instance

end LogicEMCNTDB45

end
