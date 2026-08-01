module

public import Neighborhood.Logic.Logic.ET5

@[expose] public section

variable {α : Type u}

namespace LogicETDB5

/-- The axiom schemes `D` and `B` are redundant over `T` and `5`. -/
theorem eq_LogicET5 : (@LogicETDB5 α) = LogicET5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomT | exact Logic.axiomD | exact Logic.axiomB | exact Logic.axiomFive
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicETDB5

end
