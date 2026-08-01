module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

namespace LogicEMNDB

/-- The axiom `N` is redundant over `M`, `D`, and `B`. -/
theorem eq_LogicEMDB : (@LogicEMNDB α) = LogicEMDB := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomN | exact Logic.axiomD | exact Logic.axiomB
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicEMNDB

end
