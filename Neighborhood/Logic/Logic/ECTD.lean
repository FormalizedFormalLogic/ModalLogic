module

public import Neighborhood.Logic.Logic.ECD
public import Neighborhood.Logic.Logic.ECT

@[expose] public section

variable {α : Type u}

namespace LogicECTD

/-- The axiom scheme `D` is redundant over `C` and `T`. -/
theorem eq_LogicECT : (@LogicECTD α) = LogicECT := by
  hilbert_eq_axioms

theorem ssubset_LogicECD : @LogicECD ℕ ⊂ LogicECTD := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECD.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, ProvableHilbert.axm (by grind), hA⟩

end LogicECTD

end
