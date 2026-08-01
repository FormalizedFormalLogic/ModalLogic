module

public import Neighborhood.Logic.Logic.ET5

@[expose] public section

variable {α : Type u}

namespace LogicETP5

/-- The axiom `P` is redundant over `T`. -/
theorem eq_LogicET5 : (@LogicETP5 α) = LogicET5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, rfl⟩ | rfl) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomP | exact Logic.axiomT | exact Logic.axiomFive
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicETP5

end
