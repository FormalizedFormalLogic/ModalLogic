module

public import Neighborhood.Logic.Logic.ET5
public import Neighborhood.Logic.Logic.EB45

@[expose] public section

variable {α : Type u}

namespace LogicETB45

/-- The axiom scheme `B` and the axiom scheme `4` are redundant over `T` and `5`. -/
theorem eq_LogicET5 : (@LogicETB45 α) = LogicET5 := by
  hilbert_eq_axioms

theorem ssubset_LogicEB45 : @LogicEB45 ℕ ⊂ LogicETB45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEB45.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, ProvableHilbert.axm (by grind), hA⟩

end LogicETB45

end
