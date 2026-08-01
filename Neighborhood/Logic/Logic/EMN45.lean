module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

namespace LogicEMN45

/-- The axiom `N` is redundant over `M`, `4` and `5`. -/
theorem eq_LogicEM45 : (@LogicEMN45 α) = LogicEM45 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first
        | exact Logic.axiomM
        | exact Logic.axiomFour
        | exact Logic.axiomFive
        | exact Logic.axiomN
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicEMN45

end
