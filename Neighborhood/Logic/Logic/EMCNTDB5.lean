module

public import Neighborhood.Logic.Logic.EMCNTDB45

@[expose] public section

variable {α : Type u}

namespace LogicEMCNTDB5

/-- The axiom `4` is redundant over `M`, `C`, `N`, `T`, `D`, `B`, `5`. -/
theorem eq_LogicEMCNTDB45 : (@LogicEMCNTDB5 α) = LogicEMCNTDB45 := by
  hilbert_eq_axioms

instance : (@LogicEMCNTDB5 α).IsConsistent := by
  rw [eq_LogicEMCNTDB45]; infer_instance

end LogicEMCNTDB5

end
