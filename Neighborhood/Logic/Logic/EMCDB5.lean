module

public import Neighborhood.Logic.Logic.ECDB5
public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEMCDB5

/-- Over `M`, `T`, and `5`, the axiom schemes `C`, `D`, and `B` axiomatise the same logic. -/
theorem eq_LogicEMT5 : (@LogicEMCDB5 α) = LogicEMT5 := by
  hilbert_eq_axioms

theorem ssubset_LogicECDB5 : @LogicECDB5 ℕ ⊂ LogicEMCDB5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicECDB5.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, ProvableHilbert.axm (by grind), hA⟩

end LogicEMCDB5

end
