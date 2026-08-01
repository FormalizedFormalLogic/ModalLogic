module

public import Neighborhood.Logic.Logic.ETB

@[expose] public section

variable {α : Type u}

namespace LogicETPB

/-- The axiom `P` is redundant over `T`. -/
theorem eq_LogicETB : (@LogicETPB α) = LogicETB := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, rfl⟩ | rfl) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomP | exact Logic.axiomT | exact Logic.axiomB
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicETPB

end
