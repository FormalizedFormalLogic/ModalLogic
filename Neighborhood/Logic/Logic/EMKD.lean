module

public import Neighborhood.Logic.Logic.EMCD

@[expose] public section

variable {α : Type u}

namespace LogicEMKD

/-- Over `EMD`, the axiom scheme `K` and the axiom scheme `C` axiomatise the same logic. -/
theorem eq_LogicEMCD : (@LogicEMKD α) = LogicEMCD := by
  hilbert_eq_axioms

end LogicEMKD

end
