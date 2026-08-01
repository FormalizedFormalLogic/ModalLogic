module

public import Neighborhood.Logic.Logic.EMCNTDB45

@[expose] public section

variable {α : Type u}

namespace LogicEMCTB45

/-- The axioms `N`, `D` are redundant over `M`, `C`, `T`, `B`, `4`, `5`. -/
theorem eq_LogicEMCNTDB45 : (@LogicEMCTB45 α) = LogicEMCNTDB45 := by
  hilbert_eq_axioms

instance : (@LogicEMCTB45 α).IsConsistent := by
  rw [eq_LogicEMCNTDB45]; infer_instance

end LogicEMCTB45

end
