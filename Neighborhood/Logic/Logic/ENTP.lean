module

public import Neighborhood.Logic.Logic.ENT

@[expose] public section

variable {α : Type u}

namespace LogicENTP

/-- The axiom `P` is redundant over `N` and `T`. -/
theorem eq_LogicENT : (@LogicENTP α) = LogicENT := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((rfl | ⟨B, rfl⟩) | rfl) <;>
      first | exact Logic.axiomN | exact Logic.axiomP | exact Logic.axiomT
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicENTP

end
