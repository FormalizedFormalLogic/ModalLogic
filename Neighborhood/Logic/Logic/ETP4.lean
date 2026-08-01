module

public import Neighborhood.Logic.Logic.ET4

@[expose] public section

variable {α : Type u}

namespace LogicETP4

/-- The axiom `P` is redundant over `T`. -/
theorem eq_LogicET4 : (@LogicETP4 α) = LogicET4 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, rfl⟩ | rfl) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomP | exact Logic.axiomT | exact Logic.axiomFour
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicETP4

end
