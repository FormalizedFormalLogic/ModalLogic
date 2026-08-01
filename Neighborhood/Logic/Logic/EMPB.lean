module

public import Neighborhood.Logic.Logic.EMDB

@[expose] public section

variable {α : Type u}

namespace LogicEMPB

/-- Over `EMB`, the axiom `P` and the axiom scheme `D` axiomatise the same logic. -/
theorem eq_LogicEMDB : (@LogicEMPB α) = LogicEMDB := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomP | exact Logic.axiomB
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomD | exact Logic.axiomB

end LogicEMPB

end
