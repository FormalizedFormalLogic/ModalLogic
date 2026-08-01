module

public import Neighborhood.Logic.Logic.EMCNTDB45

@[expose] public section

variable {α : Type u}

namespace LogicEMCNTB45

/-- The axiom `D` is redundant over `M`, `C`, `N`, `T`, `B`, `4`, `5`. -/
theorem eq_LogicEMCNTDB45 : (@LogicEMCNTB45 α) = LogicEMCNTDB45 := by
  hilbert_eq_axioms

instance : (@LogicEMCNTB45 α).IsConsistent := by
  rw [eq_LogicEMCNTDB45]; infer_instance

end LogicEMCNTB45

end
