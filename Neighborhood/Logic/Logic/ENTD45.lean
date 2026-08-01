module

public import Neighborhood.Logic.Logic.ET5
public import Neighborhood.Logic.Logic.END45

@[expose] public section

variable {α : Type u}

namespace LogicENTD45

/-- Over `ET5`, the axiom schemes `N`, `D`, and `4` are redundant. -/
theorem eq_LogicET5 : (@LogicENTD45 α) = LogicET5 := by
  hilbert_eq_axioms

theorem ssubset_LogicEND45 : @LogicEND45 ℕ ⊂ LogicENTD45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEND45.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, ProvableHilbert.axm (by grind), hA⟩

end LogicENTD45

end
