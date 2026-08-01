module

public import Neighborhood.Logic.Logic.EMCNTDB45

@[expose] public section

variable {α : Type u}

namespace LogicEMNDB45

/-- The axioms `C`, `T` are redundant over `M`, `N`, `D`, `B`, `4`, `5`. -/
theorem eq_LogicEMCNTDB45 : (@LogicEMNDB45 α) = LogicEMCNTDB45 := by
  hilbert_eq_axioms

instance : (@LogicEMNDB45 α).IsConsistent := by
  rw [eq_LogicEMCNTDB45]; infer_instance

end LogicEMNDB45

end
