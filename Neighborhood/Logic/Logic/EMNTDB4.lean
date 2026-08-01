module

public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEMNTDB4

/-- The axioms `N`, `D`, `B`, `4` are redundant over `M`, `T`, `5`; conversely `5` is derivable over
`M`, `N`, `T`, `D`, `B`, `4`. -/
theorem eq_LogicEMT5 : (@LogicEMNTDB4 α) = LogicEMT5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomN | exact Logic.axiomT | exact Logic.axiomD |
        exact Logic.axiomB | exact Logic.axiomFour
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomT | exact Logic.axiomFive

instance : (@LogicEMNTDB4 α).IsConsistent := by
  rw [eq_LogicEMT5]; infer_instance

end LogicEMNTDB4

end
