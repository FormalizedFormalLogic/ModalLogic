module

public import Neighborhood.Logic.Logic.ECT5

@[expose] public section

variable {α : Type u}

namespace LogicECNTDB4

/-- The axioms `N`, `D`, `B`, `4` are redundant over `C`, `T`, `5`; conversely `5` is derivable over
`C`, `N`, `T`, `D`, `B`, `4`. -/
theorem eq_LogicECT5 : (@LogicECNTDB4 α) = LogicECT5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomT | exact Logic.axiomD |
        exact Logic.axiomB | exact Logic.axiomFour
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomC | exact Logic.axiomT | exact Logic.axiomFive

instance : (@LogicECNTDB4 α).IsConsistent := by
  rw [eq_LogicECT5]; infer_instance

end LogicECNTDB4

end
