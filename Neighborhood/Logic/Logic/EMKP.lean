module

public import Neighborhood.Logic.Logic.EMCD

@[expose] public section

variable {α : Type u}

namespace LogicEMKP

/-- Over `EM`, the axiom schemes `K` and `P` axiomatise the same logic as the axiom schemes
`C` and `D`. -/
theorem eq_LogicEMCD : (@LogicEMKP α) = LogicEMCD := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | rfl) <;>
      first | exact Logic.axiomM | exact Logic.axiomK | exact Logic.axiomP
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomD

end LogicEMKP

end
