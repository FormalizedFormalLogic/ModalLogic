module

public import Neighborhood.Logic.Logic.EMCNTDB45

@[expose] public section

variable {α : Type u}

namespace LogicEMNTB45

/-- The axioms `C`, `D` are redundant over `M`, `N`, `T`, `B`, `4`, `5`. -/
theorem eq_LogicEMCNTDB45 : (@LogicEMNTB45 α) = LogicEMCNTDB45 := by
  hilbert_eq_axioms

instance : (@LogicEMNTB45 α).IsConsistent := by
  rw [eq_LogicEMCNTDB45]; infer_instance

end LogicEMNTB45

end
