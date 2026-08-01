module

public import Neighborhood.Logic.Logic.EMB4
public import Neighborhood.Logic.Logic.ECB45

@[expose] public section

variable {α : Type u}

namespace LogicEMCB45

/-- The axiom schemes `C` and `5` are redundant over `M`, `B` and `4`. -/
theorem eq_LogicEMB4 : (@LogicEMCB45 α) = LogicEMB4 := by
  hilbert_eq_axioms

theorem ssubset_LogicECB45 : @LogicECB45 ℕ ⊂ LogicEMCB45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicECB45.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, ProvableHilbert.axm (by grind), hA⟩

end LogicEMCB45

end
