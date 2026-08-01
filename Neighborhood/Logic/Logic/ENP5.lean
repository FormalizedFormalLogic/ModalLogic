module

public import Neighborhood.Logic.Logic.EP5

@[expose] public section

variable {α : Type u}

namespace LogicENP5

/-- The axiom `N` is redundant over `P` and `5`. -/
theorem eq_LogicEP5 : (@LogicENP5 α) = LogicEP5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((rfl | rfl) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomP | exact Logic.axiomFive
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicENP5

end
