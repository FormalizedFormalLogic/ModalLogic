module

public import Neighborhood.Logic.Logic.EMCNTDB45

@[expose] public section

variable {α : Type u}

namespace LogicEMNTDB5

/-- The axioms `C`, `4` are redundant over `M`, `N`, `T`, `D`, `B`, `5`. -/
theorem eq_LogicEMCNTDB45 : (@LogicEMNTDB5 α) = LogicEMCNTDB45 := by
  hilbert_eq_axioms

instance : (@LogicEMNTDB5 α).IsConsistent := by
  rw [eq_LogicEMCNTDB45]; infer_instance

end LogicEMNTDB5

end
