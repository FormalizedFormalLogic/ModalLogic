module

public import Neighborhood.Logic.Logic.ETB

@[expose] public section

variable {α : Type u}

namespace LogicETDB

/-- The axiom `D` is redundant over `T` and `B`. -/
theorem eq_LogicETB : (@LogicETDB α) = LogicETB := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomT | exact Logic.axiomD | exact Logic.axiomB
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicETDB

end
