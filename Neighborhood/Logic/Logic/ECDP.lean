module

public import Neighborhood.Logic.Logic.ECP

@[expose] public section

variable {α : Type u}

namespace LogicECDP

/-- The axiom scheme `D` is redundant over `C` and `P`. -/
theorem eq_LogicECP : (@LogicECDP α) = LogicECP := by
  hilbert_eq_axioms

end LogicECDP

end
