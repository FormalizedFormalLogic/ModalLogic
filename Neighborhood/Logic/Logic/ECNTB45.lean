module

public import Neighborhood.Logic.Logic.ECNTDB45

@[expose] public section

variable {α : Type u}

namespace LogicECNTB45

/-- The axiom `D` is redundant over `C`, `N`, `T`, `B`, `4`, `5`. -/
theorem eq_LogicECNTDB45 : (@LogicECNTB45 α) = LogicECNTDB45 := by
  hilbert_eq_axioms

instance : (@LogicECNTB45 α).IsConsistent := by
  rw [eq_LogicECNTDB45]; infer_instance

end LogicECNTB45

end
