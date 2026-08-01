module

public import Neighborhood.Logic.Logic.ECT5
public import Neighborhood.Logic.Logic.ECND5

@[expose] public section

variable {α : Type u}

namespace LogicECNTD5

/-- The axiom schemes `N` and `D` are redundant over `C`, `T`, and `Five`. -/
theorem eq_LogicECT5 : (@LogicECNTD5 α) = LogicECT5 := by
  hilbert_eq_axioms

theorem ssubset_LogicECND5 : @LogicECND5 ℕ ⊂ LogicECNTD5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECND5.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, ProvableHilbert.axm (by grind), hA⟩

end LogicECNTD5

end
