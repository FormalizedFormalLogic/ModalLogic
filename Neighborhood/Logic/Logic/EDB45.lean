module

public import Neighborhood.Logic.Logic.ET5

@[expose] public section

variable {α : Type u}

namespace LogicEDB45

/-- The axiom schemes `D`, `B`, `4` and `5` axiomatise the same logic as `T` and `5`. -/
theorem eq_LogicET5 : (@LogicEDB45 α) = LogicET5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomD | exact Logic.axiomB | exact Logic.axiomFour | exact Logic.axiomFive
  · apply Hilbert.subset_of_provable_axioms
    rintro A (⟨B, rfl⟩ | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomT | exact Logic.axiomFive

end LogicEDB45

end
