module

public import Neighborhood.Logic.Logic.ECNTDB45

@[expose] public section

variable {α : Type u}

namespace LogicECNTDB4

/-- The axiom `5` is redundant over `C`, `N`, `T`, `D`, `B`, `4`. -/
theorem eq_LogicECNTDB45 : (@LogicECNTDB4 α) = LogicECNTDB45 := by
  hilbert_eq_axioms

instance : (@LogicECNTDB4 α).IsConsistent := by
  rw [eq_LogicECNTDB45]; infer_instance

end LogicECNTDB4

end
