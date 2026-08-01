module

public import Neighborhood.Logic.Logic.EMB4

@[expose] public section

variable {α : Type u}

namespace LogicEMB5

/-- Over `EMB`, the axiom scheme `5` and the axiom scheme `4` axiomatise the same logic. -/
theorem eq_LogicEMB4 : (@LogicEMB5 α) = LogicEMB4 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomB | exact Logic.axiomFive
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomB | exact Logic.axiomFour

end LogicEMB5

end
