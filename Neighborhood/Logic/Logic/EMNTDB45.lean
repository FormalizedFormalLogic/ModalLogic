module

public import Neighborhood.Logic.Logic.EMCNTDB45

@[expose] public section

variable {α : Type u}

namespace LogicEMNTDB45

/-- The axiom `C` is redundant over `M`, `N`, `T`, `D`, `B`, `4`, `5`. -/
theorem eq_LogicEMCNTDB45 : (@LogicEMNTDB45 α) = LogicEMCNTDB45 := by
  hilbert_eq_axioms

instance : (@LogicEMNTDB45 α).IsConsistent := by
  rw [eq_LogicEMCNTDB45]; infer_instance

end LogicEMNTDB45

end
