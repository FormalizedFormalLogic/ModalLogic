module

public import Neighborhood.Logic.Logic.ET5
public import Neighborhood.Logic.Logic.ED5

@[expose] public section

variable {α : Type u}

namespace LogicETD5

/-- The axiom `D` is redundant over `T`. -/
theorem eq_LogicET5 : (@LogicETD5 α) = LogicET5 := by
  hilbert_eq_axioms

theorem ssubset_LogicED5 : @LogicED5 ℕ ⊂ LogicETD5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicED5.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, ProvableHilbert.axm (by grind), hA⟩

end LogicETD5

end
