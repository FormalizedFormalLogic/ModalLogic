module

public import Neighborhood.Logic.Logic.EKP

@[expose] public section

variable {α : Type u}

namespace LogicEKDP

/-- The axiom `D` is redundant over `K` and `P`. -/
theorem eq_LogicEKP : (@LogicEKDP α) = LogicEKP := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, rfl⟩) | rfl) <;>
      first | exact Logic.axiomK | exact Logic.axiomP | exact Logic.axiomD
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicEKDP

end
