module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

namespace LogicEMCB4

/-- The axiom scheme `C` is redundant over `M`, `B`, and `4`. -/
theorem eq_LogicEMB4 : (@LogicEMCB4 α) = LogicEMB4 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomB | exact Logic.axiomFour
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicEMCB4

end
