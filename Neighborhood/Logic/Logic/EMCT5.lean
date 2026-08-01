module

public import Neighborhood.Hilbert.Logics
public import Neighborhood.Logic.Logic.EMCT

@[expose] public section

variable {α : Type u}

namespace LogicEMCT5

/-- The axiom scheme `C` is redundant over `M`, `T`, and `5`. -/
theorem eq_LogicEMT5 : (@LogicEMCT5 α) = LogicEMT5 := by
  hilbert_eq_axioms

theorem ssubset_LogicEMCT : @LogicEMCT ℕ ⊂ LogicEMCT5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEMCT.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, ProvableHilbert.axm (by grind), hA⟩

end LogicEMCT5

end
