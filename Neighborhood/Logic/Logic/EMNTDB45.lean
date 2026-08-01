module

public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u}

namespace LogicEMNTDB45

/-- The axioms `N`, `D`, `B`, `4` are redundant over `M`, `T`, `5`. -/
theorem eq_LogicEMT5 : (@LogicEMNTDB45 α) = LogicEMT5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((((((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) |
      ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomN | exact Logic.axiomT | exact Logic.axiomD |
        exact Logic.axiomB | exact Logic.axiomFour | exact Logic.axiomFive
  · exact Hilbert.subset_of_subset_axioms (by grind (instances := 4000))

instance : (@LogicEMNTDB45 α).IsConsistent := by
  rw [eq_LogicEMT5]; infer_instance

end LogicEMNTDB45

end
