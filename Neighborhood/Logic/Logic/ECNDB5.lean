module

public import Neighborhood.Logic.Logic.ECDB5

@[expose] public section

variable {α : Type u}

namespace LogicECNDB5

/-- The axiom scheme `N` is redundant over `C`, `D`, `B`, and `Five`. -/
theorem eq_LogicECDB5 : (@LogicECNDB5 α) = LogicECDB5 := by
  hilbert_eq_axioms

end LogicECNDB5

end
