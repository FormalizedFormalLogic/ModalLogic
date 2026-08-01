module

public import Neighborhood.Logic.Logic.ECNTDB45

@[expose] public section

variable {α : Type u}

namespace LogicECNDB45

/-- The axiom `T` is redundant over `C`, `N`, `D`, `B`, `4`, `5`. -/
theorem eq_LogicECNTDB45 : (@LogicECNDB45 α) = LogicECNTDB45 := by
  hilbert_eq_axioms

instance : (@LogicECNDB45 α).IsConsistent := by
  rw [eq_LogicECNTDB45]; infer_instance

end LogicECNDB45

end
