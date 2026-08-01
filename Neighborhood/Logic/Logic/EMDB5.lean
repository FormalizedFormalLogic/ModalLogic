module

public import Neighborhood.Logic.Logic.EMT5
public import Neighborhood.Logic.Logic.EDB5

@[expose] public section

variable {α : Type u}

namespace LogicEMDB5

/-- Over `M`, `D`, `B`, and `5` axiomatise the same logic as `M`, `T`, and `5`. -/
theorem eq_LogicEMT5 : (@LogicEMDB5 α) = LogicEMT5 := by
  hilbert_eq_axioms

theorem ssubset_LogicEDB5 : @LogicEDB5 ℕ ⊂ LogicEMDB5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicEDB5.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, ProvableHilbert.axm (by grind), hA⟩

end LogicEMDB5

end
