module

public import Neighborhood.Logic.Logic.ET

@[expose] public section

variable {α : Type u}

namespace LogicETDP

/-- The axioms `D` and `P` are redundant over `T`. -/
theorem eq_LogicET : (@LogicETDP α) = LogicET := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, rfl⟩ | ⟨B, rfl⟩) | rfl) <;>
      first | exact Logic.axiomP | exact Logic.axiomT | exact Logic.axiomD
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicETDP

end
