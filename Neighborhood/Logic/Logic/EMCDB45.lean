module

public import Neighborhood.Logic.Logic.EMCNTDB45

@[expose] public section

variable {α : Type u}

namespace LogicEMCDB45

/-- The axioms `N`, `T` are redundant over `M`, `C`, `D`, `B`, `4`, `5`. -/
theorem eq_LogicEMCNTDB45 : (@LogicEMCDB45 α) = LogicEMCNTDB45 := by
  hilbert_eq_axioms

instance : (@LogicEMCDB45 α).IsConsistent := by
  rw [eq_LogicEMCNTDB45]; infer_instance

end LogicEMCDB45

end
