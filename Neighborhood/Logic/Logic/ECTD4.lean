module

public import Neighborhood.Logic.Logic.ECT4

@[expose] public section

variable {α : Type u}

namespace LogicECTD4

/-- The axiom scheme `D` is redundant over `C`, `T`, and `4`. -/
theorem eq_LogicECT4 : (@LogicECTD4 α) = LogicECT4 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomC | exact Logic.axiomT | exact Logic.axiomD | exact Logic.axiomFour
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicECTD4

end
