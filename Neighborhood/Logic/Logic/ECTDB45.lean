module

public import Neighborhood.Logic.Logic.ECT5

@[expose] public section

variable {α : Type u}

namespace LogicECTDB45

/-- The axioms `D`, `B`, `4` are redundant over `C`, `T`, `5`. -/
theorem eq_LogicECT5 : (@LogicECTDB45 α) = LogicECT5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomC | exact Logic.axiomT | exact Logic.axiomD | exact Logic.axiomB |
        exact Logic.axiomFour | exact Logic.axiomFive
  · exact Hilbert.subset_of_subset_axioms (by grind (instances := 4000))

instance : (@LogicECTDB45 α).IsConsistent := by
  rw [eq_LogicECT5]; infer_instance

end LogicECTDB45

end
