module

public import Neighborhood.Logic.Logic.EKT

@[expose] public section

variable {α : Type u}

namespace LogicEKTD

/-- The axiom `D` is redundant over `K` and `T`. -/
theorem eq_LogicEKT : (@LogicEKTD α) = LogicEKT := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomK | exact Logic.axiomT | exact Logic.axiomD
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicEKTD

end
