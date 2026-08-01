module

public import Neighborhood.Logic.Logic.EMCD4
public import Neighborhood.Logic.Logic.EMCT4

@[expose] public section

variable {α : Type u}

namespace LogicEMCTD4

/-- The axiom scheme `D` is redundant over `M`, `C`, `T` and `4`. -/
theorem eq_LogicEMCT4 : (@LogicEMCTD4 α) = LogicEMCT4 := by
  hilbert_eq_axioms

theorem ssubset_LogicEMCD4 : @LogicEMCD4 ℕ ⊂ LogicEMCTD4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEMCD4.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, ProvableHilbert.axm (by grind), hA⟩

end LogicEMCTD4

end
