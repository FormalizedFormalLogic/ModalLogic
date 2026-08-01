module

public import Neighborhood.Logic.Logic.ECT5

@[expose] public section

variable {α : Type u}

namespace LogicECNDB45

/-- The axioms `N`, `D`, `B`, `4` are redundant over `C`, `T`, `5`; conversely `T` is derivable over
`C`, `N`, `D`, `B`, `4`, `5`. -/
theorem eq_LogicECT5 : (@LogicECNDB45 α) = LogicECT5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomD | exact Logic.axiomB |
        exact Logic.axiomFour | exact Logic.axiomFive
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomC | exact Logic.axiomT | exact Logic.axiomFive

instance : (@LogicECNDB45 α).IsConsistent := by
  rw [eq_LogicECT5]; infer_instance

end LogicECNDB45

end
