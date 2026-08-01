module

public import Neighborhood.Logic.Logic.ET5

@[expose] public section

variable {α : Type u}

namespace LogicENTDB45

/-- The axioms `N`, `D`, `B`, `4` are redundant over `T`, `5`. -/
theorem eq_LogicET5 : (@LogicENTDB45 α) = LogicET5 := by
  hilbert_eq_axioms

instance : (@LogicENTDB45 α).IsConsistent := by
  rw [eq_LogicET5]; infer_instance

end LogicENTDB45

end
