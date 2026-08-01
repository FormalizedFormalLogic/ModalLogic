module

public import Neighborhood.Logic.Logic.EM45
public import Neighborhood.Logic.Logic.EMB4

@[expose] public section

variable {α : Type u}

namespace LogicEMB45

/-- The axiom scheme `5` is redundant over `M`, `B`, and `4`. -/
theorem eq_LogicEMB4 : (@LogicEMB45 α) = LogicEMB4 := by
  hilbert_eq_axioms

theorem ssubset_LogicEM45 : @LogicEM45 ℕ ⊂ LogicEMB45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEM45.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, ProvableHilbert.axm (by grind), hA⟩

end LogicEMB45

end
