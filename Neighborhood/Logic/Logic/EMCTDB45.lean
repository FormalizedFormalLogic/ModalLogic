module

public import Neighborhood.Logic.Logic.EMCNTDB45

@[expose] public section

variable {α : Type u}

namespace LogicEMCTDB45

/-- The axiom `N` is redundant over `M`, `C`, `T`, `D`, `B`, `4`, `5`. -/
theorem eq_LogicEMCNTDB45 : (@LogicEMCTDB45 α) = LogicEMCNTDB45 := by
  hilbert_eq_axioms

instance : (@LogicEMCTDB45 α).IsConsistent := by
  rw [eq_LogicEMCNTDB45]; infer_instance

end LogicEMCTDB45

end
