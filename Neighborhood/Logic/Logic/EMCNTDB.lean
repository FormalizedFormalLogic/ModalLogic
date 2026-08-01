module

public import Neighborhood.Logic.Logic.EMTB

@[expose] public section

variable {α : Type u}

namespace LogicEMCNTDB

/-- The axioms `C`, `N`, `D` are redundant over `M`, `T`, `B`. -/
theorem eq_LogicEMTB : (@LogicEMCNTDB α) = LogicEMTB := by
  hilbert_eq_axioms

instance : (@LogicEMCNTDB α).IsConsistent := by
  rw [eq_LogicEMTB]; infer_instance

end LogicEMCNTDB

end
