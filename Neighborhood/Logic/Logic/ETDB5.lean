module

public import Neighborhood.Logic.Logic.ET5
public import Neighborhood.Logic.Logic.EDB5

@[expose] public section

variable {α : Type u}

namespace LogicETDB5

/-- The axiom schemes `D` and `B` are redundant over `T` and `5`. -/
theorem eq_LogicET5 : (@LogicETDB5 α) = LogicET5 := by
  hilbert_eq_axioms

theorem ssubset_LogicEDB5 : @LogicEDB5 ℕ ⊂ LogicETDB5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEDB5.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, ProvableHilbert.axm (by grind), hA⟩

end LogicETDB5

end
