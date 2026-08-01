module

public import Neighborhood.Logic.Logic.END5

@[expose] public section

variable {α : Type u}

namespace LogicEDP5

/-- `EDP5` and `END5` axiomatise the same logic: `P` is derivable from `D` and `N`, while
conversely `N` is derivable from `P` and `5`. -/
theorem eq_LogicEND5 : (@LogicEDP5 α) = LogicEND5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, rfl⟩ | rfl) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomD | exact Logic.axiomP | exact Logic.axiomFive
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((rfl | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomD | exact Logic.axiomFive

end LogicEDP5

end
