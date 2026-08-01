module

public import Neighborhood.Logic.Logic.ENT4

@[expose] public section

variable {α : Type u}

namespace LogicENTD4

/-- The axiom scheme `D` is redundant over `N`, `T` and `4`. -/
theorem eq_LogicENT4 : (@LogicENTD4 α) = LogicENT4 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((rfl | ⟨B, rfl⟩) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomT | exact Logic.axiomD | exact Logic.axiomFour
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicENTD4

end
