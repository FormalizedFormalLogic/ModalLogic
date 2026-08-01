module

public import Neighborhood.Logic.Logic.EMC5

@[expose] public section

variable {α : Type u}

namespace LogicEMK5

/-- Over `EM5`, the axiom scheme `K` and the axiom scheme `C` axiomatise the same logic. -/
theorem eq_LogicEMC5 : (@LogicEMK5 α) = LogicEMC5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomK | exact Logic.axiomFive
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomFive

end LogicEMK5

end
