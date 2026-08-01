module

public import Neighborhood.Logic.Logic.ENT

@[expose] public section

variable {α : Type u}

namespace LogicENTD

/-- The axiom scheme `D` is redundant over `N` and `T`. -/
theorem eq_LogicENT : (@LogicENTD α) = LogicENT := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((rfl | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomT | exact Logic.axiomD
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicENTD

end
