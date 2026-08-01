module

public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEMCNTD45

/-- The axioms `C`, `N`, `D`, `4` are redundant over `M`, `T`, `5`. -/
theorem eq_LogicEMT5 : (@LogicEMCNTD45 α) = LogicEMT5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((((((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) |
      ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomT |
        exact Logic.axiomD | exact Logic.axiomFour | exact Logic.axiomFive
  · exact Hilbert.subset_of_subset_axioms (by grind (instances := 4000))

instance : (@LogicEMCNTD45 α).IsConsistent := by
  rw [eq_LogicEMT5]; infer_instance

end LogicEMCNTD45

end
