module

public import Neighborhood.Logic.Logic.ED45
public import Neighborhood.Logic.Logic.ET5

@[expose] public section

variable {α : Type u}

namespace LogicETD45

/-- Over `T`, the axiom schemes `D`, `4`, and `5` axiomatise the same logic as `5`. -/
theorem eq_LogicET5 : (@LogicETD45 α) = LogicET5 := by
  hilbert_eq_axioms

theorem ssubset_LogicED45 : @LogicED45 ℕ ⊂ LogicETD45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicED45.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, ProvableHilbert.axm (by grind), hA⟩

end LogicETD45

end
