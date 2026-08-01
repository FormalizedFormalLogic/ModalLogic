module

public import Neighborhood.Logic.Logic.EMD

@[expose] public section

variable {α : Type u}

namespace LogicEMDP

/-- The axiom `P` is redundant over `M` and `D`. -/
theorem eq_LogicEMD : (@LogicEMDP α) = LogicEMD := by
  hilbert_eq_axioms

end LogicEMDP

end
