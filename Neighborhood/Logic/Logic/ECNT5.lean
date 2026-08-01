module

public import Neighborhood.Hilbert.Logics
public import Neighborhood.Logic.Logic.ECN5

@[expose] public section

variable {α : Type u}

namespace LogicECNT5

/-- The axiom `N` is redundant over `T` and `5`. -/
theorem eq_LogicECT5 : (@LogicECNT5 α) = LogicECT5 := by
  hilbert_eq_axioms

theorem ssubset_LogicECN5 : @LogicECN5 ℕ ⊂ LogicECNT5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECN5.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, ProvableHilbert.axm (by grind), hA⟩

end LogicECNT5

end
