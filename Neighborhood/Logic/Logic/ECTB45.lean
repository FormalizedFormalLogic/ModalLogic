module

public import Neighborhood.Logic.Logic.ECT5
public import Neighborhood.Logic.Logic.ECB45

@[expose] public section

variable {α : Type u}

namespace LogicECTB45

/-- The axiom schemes `B` and `Four` are redundant over `C`, `T`, and `Five`. -/
theorem eq_LogicECT5 : (@LogicECTB45 α) = LogicECT5 := by
  hilbert_eq_axioms

theorem ssubset_LogicECB45 : @LogicECB45 ℕ ⊂ LogicECTB45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECB45.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, ProvableHilbert.axm (by grind), hA⟩

end LogicECTB45

end
