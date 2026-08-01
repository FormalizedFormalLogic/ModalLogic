module

public import Neighborhood.Logic.Logic.EMCD

@[expose] public section

variable {α : Type u}

namespace LogicEMKD

/-- Over `EMD`, the axiom scheme `K` and the axiom scheme `C` axiomatise the same logic. -/
theorem eq_LogicEMCD : (@LogicEMKD α) = LogicEMCD := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomK | exact Logic.axiomD
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomD

end LogicEMKD

end
