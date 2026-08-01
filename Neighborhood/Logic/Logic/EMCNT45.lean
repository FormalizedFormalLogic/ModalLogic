module

public import Neighborhood.Logic.Logic.EMCNTDB45

@[expose] public section

variable {α : Type u}

namespace LogicEMCNT45

/-- The axioms `D`, `B` are redundant over `M`, `C`, `N`, `T`, `4`, `5`. -/
theorem eq_LogicEMCNTDB45 : (@LogicEMCNT45 α) = LogicEMCNTDB45 := by
  hilbert_eq_axioms

instance : (@LogicEMCNT45 α).IsConsistent := by
  rw [eq_LogicEMCNTDB45]; infer_instance

end LogicEMCNT45

end
