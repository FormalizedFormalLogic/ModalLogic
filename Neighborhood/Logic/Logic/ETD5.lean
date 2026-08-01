module

public import Neighborhood.Logic.Logic.ET5

@[expose] public section

variable {α : Type u}

namespace LogicETD5

/-- The axiom `D` is redundant over `T`. -/
theorem eq_LogicET5 : (@LogicETD5 α) = LogicET5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomT | exact Logic.axiomD | exact Logic.axiomFive
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicETD5

end
