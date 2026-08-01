module

public import Neighborhood.Logic.Logic.ECNTDB45

@[expose] public section

variable {α : Type u}

namespace LogicECNTDB5

/-- The axiom `4` is redundant over `C`, `N`, `T`, `D`, `B`, `5`. -/
theorem eq_LogicECNTDB45 : (@LogicECNTDB5 α) = LogicECNTDB45 := by
  hilbert_eq_axioms

instance : (@LogicECNTDB5 α).IsConsistent := by
  rw [eq_LogicECNTDB45]; infer_instance

end LogicECNTDB5

end
