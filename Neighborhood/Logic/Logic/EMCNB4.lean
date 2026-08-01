module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

namespace LogicEMCNB4

/-- The axiom scheme `C` and the axiom `N` are both redundant over `M`, `B`, and `4`. -/
theorem eq_LogicEMB4 : (@LogicEMCNB4 α) = LogicEMB4 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first
        | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomB
        | exact Logic.axiomFour
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicEMCNB4

end
