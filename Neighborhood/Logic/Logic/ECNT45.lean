module

public import Neighborhood.Logic.Logic.ECN45
public import Neighborhood.Logic.Logic.ECT5

@[expose] public section

variable {α : Type u}

namespace LogicECNT45

/-- The axiom schemes `N` and `4` are redundant over `C`, `T` and `5`. -/
theorem eq_LogicECT5 : (@LogicECNT45 α) = LogicECT5 := by
  hilbert_eq_axioms

theorem ssubset_LogicECN45 : @LogicECN45 ℕ ⊂ LogicECNT45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECN45.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, ProvableHilbert.axm (by grind), hA⟩

end LogicECNT45

end
