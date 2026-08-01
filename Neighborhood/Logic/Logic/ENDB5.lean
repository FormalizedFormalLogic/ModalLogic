module

public import Neighborhood.Logic.Logic.EDB5

@[expose] public section

variable {α : Type u}

namespace LogicENDB5

/-- The axiom scheme `N` is redundant over `D`, `B`, and `5`. -/
theorem eq_LogicEDB5 : (@LogicENDB5 α) = LogicEDB5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomD | exact Logic.axiomB | exact Logic.axiomFive
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicENDB5

end
