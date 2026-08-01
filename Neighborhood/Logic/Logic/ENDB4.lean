module

public import Neighborhood.Logic.Logic.ET5

@[expose] public section

variable {α : Type u}

namespace LogicENDB4

/-- Over `N`, `D`, `B`, and `4` axiomatise the same logic as `T` and `5`. -/
theorem eq_LogicET5 : (@LogicENDB4 α) = LogicET5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((rfl | ⟨B, rfl⟩) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomD | exact Logic.axiomB | exact Logic.axiomFour
  · apply Hilbert.subset_of_provable_axioms
    rintro A (⟨B, rfl⟩ | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomT | exact Logic.axiomFive

end LogicENDB4

end
