module

public import Neighborhood.Logic.Logic.EMCNTDB45

@[expose] public section

variable {α : Type u}

namespace LogicEMTDB45

/-- The axioms `C`, `N` are redundant over `M`, `T`, `D`, `B`, `4`, `5`. -/
theorem eq_LogicEMCNTDB45 : (@LogicEMTDB45 α) = LogicEMCNTDB45 := by
  hilbert_eq_axioms

instance : (@LogicEMTDB45 α).IsConsistent := by
  rw [eq_LogicEMCNTDB45]; infer_instance

end LogicEMTDB45

end
