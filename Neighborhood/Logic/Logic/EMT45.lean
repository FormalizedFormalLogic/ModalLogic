module

public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEMT45

/-- The axiom scheme `4` is redundant over `M`, `T` and `5`. -/
theorem eq_LogicEMT5 : (@LogicEMT45 α) = LogicEMT5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomT | exact Logic.axiomFour | exact Logic.axiomFive
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicEMT45

end
