module

public import Neighborhood.Logic.Logic.ECT5

@[expose] public section

variable {α : Type u}

namespace LogicECTD5

/-- The axiom scheme `D` is redundant over `C`, `T`, and `5`. -/
theorem eq_LogicECT5 : (@LogicECTD5 α) = LogicECT5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomC | exact Logic.axiomT | exact Logic.axiomD | exact Logic.axiomFive
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicECTD5

end
