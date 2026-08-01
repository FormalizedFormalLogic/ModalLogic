module

public import Neighborhood.Logic.Logic.ECT5
public import Neighborhood.Logic.Logic.ECD45

@[expose] public section

variable {α : Type u}

namespace LogicECTD45

/-- Over `ECT5`, the axiom schemes `D` and `4` are redundant. -/
theorem eq_LogicECT5 : (@LogicECTD45 α) = LogicECT5 := by
  hilbert_eq_axioms

theorem ssubset_LogicECD45 : @LogicECD45 ℕ ⊂ LogicECTD45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECD45.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, ProvableHilbert.axm (by grind), hA⟩

end LogicECTD45

end
