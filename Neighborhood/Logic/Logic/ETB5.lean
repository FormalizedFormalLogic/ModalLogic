module

public import Neighborhood.Logic.Logic.ET5

@[expose] public section

variable {α : Type u}

namespace LogicETB5

/-- The axiom `B` is redundant over `T` and `5`. -/
theorem eq_LogicET5 : (@LogicETB5 α) = LogicET5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomT | exact Logic.axiomB | exact Logic.axiomFive
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicETB5

end
