module

public import Neighborhood.Logic.Logic.ECT5

@[expose] public section

variable {α : Type u}

namespace LogicECNTDB5

/-- The axioms `N`, `D`, `B` are redundant over `C`, `T`, `5`. -/
theorem eq_LogicECT5 : (@LogicECNTDB5 α) = LogicECT5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomT | exact Logic.axiomD |
        exact Logic.axiomB | exact Logic.axiomFive
  · exact Hilbert.subset_of_subset_axioms (by grind (instances := 4000))

instance : (@LogicECNTDB5 α).IsConsistent := by
  rw [eq_LogicECT5]; infer_instance

end LogicECNTDB5

end
