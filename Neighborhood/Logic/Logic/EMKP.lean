module

public import Neighborhood.Logic.Logic.EMCD

@[expose] public section

variable {α : Type u}

namespace LogicEMKP

/-- Over `EM`, the axiom schemes `K` and `P` axiomatise the same logic as the axiom schemes
`C` and `D`. -/
theorem eq_LogicEMCD : (@LogicEMKP α) = LogicEMCD := by
  hilbert_eq_axioms

end LogicEMKP

end
