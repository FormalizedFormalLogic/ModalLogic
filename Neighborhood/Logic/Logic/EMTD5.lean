module

public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEMTD5

/-- The axiom scheme `D` is redundant over `M`, `T` and `5`. -/
theorem eq_LogicEMT5 : (@LogicEMTD5 α) = LogicEMT5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomT | exact Logic.axiomD | exact Logic.axiomFive
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicEMTD5

end
