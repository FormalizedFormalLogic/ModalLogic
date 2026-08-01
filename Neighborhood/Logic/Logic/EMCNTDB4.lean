module

public import Neighborhood.Logic.Logic.EMCNTDB45

@[expose] public section

variable {α : Type u}

namespace LogicEMCNTDB4

/-- The axiom `5` is redundant over `M`, `C`, `N`, `T`, `D`, `B`, `4`. -/
theorem eq_LogicEMCNTDB45 : (@LogicEMCNTDB4 α) = LogicEMCNTDB45 := by
  hilbert_eq_axioms

instance : (@LogicEMCNTDB4 α).IsConsistent := by
  rw [eq_LogicEMCNTDB45]; infer_instance

end LogicEMCNTDB4

end
