module

public import Neighborhood.Logic.Logic.ECT5

@[expose] public section

variable {α : Type u}

namespace LogicECTB4

/-- The axiom scheme `B` is redundant over `C`, `T` and `5`, and the axiom scheme `4` is derivable
over `C`, `T`, `B` and `4`. -/
theorem eq_LogicECT5 : (@LogicECTB4 α) = LogicECT5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomC | exact Logic.axiomT | exact Logic.axiomB | exact Logic.axiomFour
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomC | exact Logic.axiomT | exact Logic.axiomFive

end LogicECTB4

end
