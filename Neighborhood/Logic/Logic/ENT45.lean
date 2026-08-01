module

public import Neighborhood.Logic.Logic.ET5

@[expose] public section

variable {α : Type u}

namespace LogicENT45

/-- The axiom scheme `N` is redundant over `T`, `4` and `5`. -/
theorem eq_LogicET5 : (@LogicENT45 α) = LogicET5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((rfl | ⟨B, rfl⟩) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomT | exact Logic.axiomFour | exact Logic.axiomFive
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicENT45

end
