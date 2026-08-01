module

public import Neighborhood.Logic.Logic.ENKD

@[expose] public section

variable {α : Type u}

namespace LogicENKP

/-- `ENKP` and `ENKD` axiomatise the same logic: `D` is derivable from `K` and `P`, while
conversely `P` is derivable from `N` and `D`. -/
theorem eq_LogicENKD : (@LogicENKP α) = LogicENKD := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((rfl | ⟨B, C, rfl⟩) | rfl) <;>
      first | exact Logic.axiomN | exact Logic.axiomK | exact Logic.axiomP
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((rfl | ⟨B, C, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomK | exact Logic.axiomD

end LogicENKP

end
