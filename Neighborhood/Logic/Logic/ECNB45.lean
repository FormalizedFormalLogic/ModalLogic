module

public import Neighborhood.Logic.Logic.ECB45
public import Neighborhood.Logic.Logic.ECN45
public import Neighborhood.Logic.Logic.ECNB5

@[expose] public section

variable {α : Type u}

namespace LogicECNB45

/-- The axiom scheme `N` is redundant over `C`, `B`, `4` and `5`. -/
theorem eq_LogicECB45 : (@LogicECNB45 α) = LogicECB45 := by
  hilbert_eq_axioms

theorem ssubset_LogicECN45 : @LogicECN45 ℕ ⊂ LogicECNB45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECN45.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, ProvableHilbert.axm (by grind), hA⟩

theorem ssubset_LogicECNB5 : @LogicECNB5 ℕ ⊂ LogicECNB45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECNB5.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, ProvableHilbert.axm (by grind), hA⟩

end LogicECNB45

end
