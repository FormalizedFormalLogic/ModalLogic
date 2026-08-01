module

public import Neighborhood.Logic.Logic.ECNTDB45

@[expose] public section

variable {α : Type u}

namespace LogicECNTD45

/-- The axiom `B` is redundant over `C`, `N`, `T`, `D`, `4`, `5`. -/
theorem eq_LogicECNTDB45 : (@LogicECNTD45 α) = LogicECNTDB45 := by
  hilbert_eq_axioms

instance : (@LogicECNTD45 α).IsConsistent := by
  rw [eq_LogicECNTDB45]; infer_instance

end LogicECNTD45

end
