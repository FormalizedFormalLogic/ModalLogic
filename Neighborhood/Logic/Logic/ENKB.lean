module

public import Neighborhood.Logic.Logic.EMB

@[expose] public section

variable {α : Type u}

namespace LogicENKB

/-- `ENKB` and `EMB` axiomatise the same logic: `M` is derivable from `K` and `N`, while
conversely `K` is derivable from `M` and `B`. -/
theorem eq_LogicEMB : (@LogicENKB α) = LogicEMB := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((rfl | ⟨B, C, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomK | exact Logic.axiomB
  · apply Hilbert.subset_of_provable_axioms
    rintro A (⟨B, C, rfl⟩ | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomB

end LogicENKB

end
