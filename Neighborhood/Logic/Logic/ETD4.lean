module

public import Neighborhood.Logic.Logic.ET4

@[expose] public section

variable {α : Type u}

namespace LogicETD4

/-- The axiom `D` is redundant over `T`. -/
theorem eq_LogicET4 : (@LogicETD4 α) = LogicET4 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomT | exact Logic.axiomD | exact Logic.axiomFour
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicETD4

end
