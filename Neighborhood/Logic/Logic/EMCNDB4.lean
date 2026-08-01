module

public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEMCNDB4

/-- The axioms `C`, `N`, `D`, `B`, `4` are redundant over `M`, `T`, `5`; conversely `T`, `5` are
derivable over `M`, `C`, `N`, `D`, `B`, `4`. -/
theorem eq_LogicEMT5 : (@LogicEMCNDB4 α) = LogicEMT5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomD |
        exact Logic.axiomB | exact Logic.axiomFour
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomT | exact Logic.axiomFive

instance : (@LogicEMCNDB4 α).IsConsistent := by
  rw [eq_LogicEMT5]; infer_instance

end LogicEMCNDB4

end
