module

public import Neighborhood.Logic.Logic.ECT5

@[expose] public section

variable {α : Type u}

namespace LogicECNTDB45

/-- The axioms `N`, `D`, `B`, `4` are redundant over `C`, `T`, `5`. -/
theorem eq_LogicECT5 : (@LogicECNTDB45 α) = LogicECT5 := by
  hilbert_eq_axioms

instance : (@LogicECNTDB45 α).IsConsistent := by
  rw [eq_LogicECT5]; infer_instance

end LogicECNTDB45

end
