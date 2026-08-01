module

public import Neighborhood.Logic.Logic.EKT

@[expose] public section

variable {α : Type u}

namespace LogicEKTP

/-- The axiom `P` is redundant over `K` and `T`. -/
theorem eq_LogicEKT : (@LogicEKTP α) = LogicEKT := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, rfl⟩) | rfl) <;>
      first | exact Logic.axiomK | exact Logic.axiomP | exact Logic.axiomT
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicEKTP

end
