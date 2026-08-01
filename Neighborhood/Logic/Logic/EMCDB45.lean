module

public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEMCDB45

/-- The axioms `C`, `D`, `B`, `4` are redundant over `M`, `T`, `5`; conversely `T` is derivable over
`M`, `C`, `D`, `B`, `4`, `5`. -/
theorem eq_LogicEMT5 : (@LogicEMCDB45 α) = LogicEMT5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomD | exact Logic.axiomB |
        exact Logic.axiomFour | exact Logic.axiomFive
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomT | exact Logic.axiomFive

instance : (@LogicEMCDB45 α).IsConsistent := by
  rw [eq_LogicEMT5]; infer_instance

end LogicEMCDB45

end
