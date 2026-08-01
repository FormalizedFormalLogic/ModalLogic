module

public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEMCNTB4

/-- The axioms `C`, `N`, `B`, `4` are redundant over `M`, `T`, `5`; conversely `5` is derivable over
`M`, `C`, `N`, `T`, `B`, `4`. -/
theorem eq_LogicEMT5 : (@LogicEMCNTB4 α) = LogicEMT5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomT |
        exact Logic.axiomB | exact Logic.axiomFour
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomT | exact Logic.axiomFive

instance : (@LogicEMCNTB4 α).IsConsistent := by
  rw [eq_LogicEMT5]; infer_instance

end LogicEMCNTB4

end
