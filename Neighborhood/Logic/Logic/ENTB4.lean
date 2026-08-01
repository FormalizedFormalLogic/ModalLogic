module

public import Neighborhood.Logic.Logic.ET5

@[expose] public section

variable {α : Type u}

namespace LogicENTB4

/-- Over `N`, the axiom schemes `T`, `B`, and `4` axiomatise the same logic as `T` and `5`. -/
theorem eq_LogicET5 : (@LogicENTB4 α) = LogicET5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomT | exact Logic.axiomB | exact Logic.axiomFour
  · apply Hilbert.subset_of_provable_axioms
    rintro A (⟨_, rfl⟩ | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomT | exact Logic.axiomFive

end LogicENTB4

end
