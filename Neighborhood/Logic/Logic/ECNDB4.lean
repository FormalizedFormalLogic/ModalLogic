module

public import Neighborhood.Logic.Logic.ECND4
public import Neighborhood.Logic.Logic.ECT5

@[expose] public section

variable {α : Type u}

namespace LogicECNDB4

/-- Over `ECT5`, the axiom schemes `N`, `D`, and `B` are redundant. -/
theorem eq_LogicECT5 : (@LogicECNDB4 α) = LogicECT5 := by
  hilbert_eq_axioms

theorem ssubset_LogicECND4 : @LogicECND4 ℕ ⊂ LogicECNDB4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECND4.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, ProvableHilbert.axm (by grind), hA⟩

end LogicECNDB4

end
