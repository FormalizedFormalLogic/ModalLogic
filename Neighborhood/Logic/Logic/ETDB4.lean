module

public import Neighborhood.Logic.Logic.ET5

@[expose] public section

variable {α : Type u}

namespace LogicETDB4

/-- Over `T`, the axiom schemes `D`, `B` and `4` axiomatise the same logic as `5`. -/
theorem eq_LogicET5 : (@LogicETDB4 α) = LogicET5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomT | exact Logic.axiomD | exact Logic.axiomB | exact Logic.axiomFour
  · apply Hilbert.subset_of_provable_axioms
    rintro A (⟨B, rfl⟩ | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomT | exact Logic.axiomFive

end LogicETDB4

end
