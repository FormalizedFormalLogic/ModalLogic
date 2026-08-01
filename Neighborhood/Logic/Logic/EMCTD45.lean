module

public import Neighborhood.Logic.Logic.EMCNTDB45

@[expose] public section

variable {α : Type u}

namespace LogicEMCTD45

/-- The axioms `N`, `B` are redundant over `M`, `C`, `T`, `D`, `4`, `5`. -/
theorem eq_LogicEMCNTDB45 : (@LogicEMCTD45 α) = LogicEMCNTDB45 := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind (instances := 20000))
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((((((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) |
      ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomT |
        exact Logic.axiomD | exact Logic.axiomB | exact Logic.axiomFour | exact Logic.axiomFive

instance : (@LogicEMCTD45 α).IsConsistent := by
  rw [eq_LogicEMCNTDB45]; infer_instance

end LogicEMCTD45

end
