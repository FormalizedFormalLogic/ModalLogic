module

public import Neighborhood.Logic.Logic.ECT5
public import Neighborhood.Logic.Logic.ECD5

@[expose] public section

variable {α : Type u}

namespace LogicECTD5

/-- The axiom scheme `D` is redundant over `C`, `T`, and `5`. -/
theorem eq_LogicECT5 : (@LogicECTD5 α) = LogicECT5 := by
  hilbert_eq_axioms

theorem ssubset_LogicECD5 : @LogicECD5 ℕ ⊂ LogicECTD5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECD5.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, ProvableHilbert.axm (by grind), hA⟩

end LogicECTD5

end
