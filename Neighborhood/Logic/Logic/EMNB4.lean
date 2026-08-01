module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

namespace LogicEMNB4

/-- The axiom `N` is redundant over `M`, `B`, and `4`. -/
theorem eq_LogicEMB4 : (@LogicEMNB4 α) = LogicEMB4 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomN | exact Logic.axiomB | exact Logic.axiomFour
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicEMNB4

end
