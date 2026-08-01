module

public import Neighborhood.Logic.Logic.ECT5
public import Neighborhood.Logic.Logic.ECNB5

@[expose] public section

variable {α : Type u}

namespace LogicECNTB5

/-- The axiom scheme `N` and the axiom scheme `B` are redundant over `C`, `T`, and `5`. -/
theorem eq_LogicECT5 : (@LogicECNTB5 α) = LogicECT5 := by
  hilbert_eq_axioms

theorem ssubset_LogicECNB5 : @LogicECNB5 ℕ ⊂ LogicECNTB5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECNB5.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, ProvableHilbert.axm (by grind), hA⟩

end LogicECNTB5

end
