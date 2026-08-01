module

public import Neighborhood.Logic.Logic.END

@[expose] public section

variable {α : Type u}

namespace LogicENDP

/-- The axiom `P` is redundant over `N` and `D`. -/
theorem eq_LogicEND : (@LogicENDP α) = LogicEND := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((rfl | ⟨B, rfl⟩) | rfl) <;>
      first | exact Logic.axiomN | exact Logic.axiomD | exact Logic.axiomP
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicENDP

end
