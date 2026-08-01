module

public import Neighborhood.Logic.Logic.ECNTDB45

@[expose] public section

variable {α : Type u}

namespace LogicECTDB45

/-- The axiom `N` is redundant over `C`, `T`, `D`, `B`, `4`, `5`. -/
theorem eq_LogicECNTDB45 : (@LogicECTDB45 α) = LogicECNTDB45 := by
  hilbert_eq_axioms

instance : (@LogicECTDB45 α).IsConsistent := by
  rw [eq_LogicECNTDB45]; infer_instance

end LogicECTDB45

end
