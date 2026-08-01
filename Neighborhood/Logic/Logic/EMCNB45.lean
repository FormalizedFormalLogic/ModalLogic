module

public import Neighborhood.Logic.Logic.EMB4

@[expose] public section

variable {α : Type u}

namespace LogicEMCNB45

/-- The axioms `C`, `N`, `5` are redundant over `M`, `B`, `4`. -/
theorem eq_LogicEMB4 : (@LogicEMCNB45 α) = LogicEMB4 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomB |
        exact Logic.axiomFour | exact Logic.axiomFive
  · exact Hilbert.subset_of_subset_axioms (by grind (instances := 20000))

instance : (@LogicEMCNB45 α).IsConsistent := by
  rw [eq_LogicEMB4]; infer_instance

end LogicEMCNB45

end
