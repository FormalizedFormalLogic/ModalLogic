module

public import Neighborhood.Logic.Logic.EMT4

@[expose] public section

variable {α : Type u}

namespace LogicEMTD4

/-- The axiom scheme `D` is redundant over `M`, `T` and `4`. -/
theorem eq_LogicEMT4 : (@LogicEMTD4 α) = LogicEMT4 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomT | exact Logic.axiomD | exact Logic.axiomFour
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicEMTD4

end
