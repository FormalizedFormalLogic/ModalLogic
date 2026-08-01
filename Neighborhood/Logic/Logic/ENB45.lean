module

public import Neighborhood.Logic.Logic.EB45

@[expose] public section

variable {α : Type u}

namespace LogicENB45

/-- The axiom `N` is redundant over `B`, `4` and `5`. -/
theorem eq_LogicEB45 : (@LogicENB45 α) = LogicEB45 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomB | exact Logic.axiomFour | exact Logic.axiomFive
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicENB45

end
