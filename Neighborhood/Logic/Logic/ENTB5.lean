module

public import Neighborhood.Logic.Logic.ET5

@[expose] public section

variable {α : Type u}

namespace LogicENTB5

/-- The axiom `N` and the axiom scheme `B` are redundant over `T` and `5`. -/
theorem eq_LogicET5 : (@LogicENTB5 α) = LogicET5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomT | exact Logic.axiomB | exact Logic.axiomFive
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicENTB5

end
