module

public import Neighborhood.Logic.Logic.ETB

@[expose] public section

variable {α : Type u}

namespace LogicENTDB

/-- The axiom `N` and the axiom scheme `D` are redundant over `T` and `B`. -/
theorem eq_LogicETB : (@LogicENTDB α) = LogicETB := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomT | exact Logic.axiomD | exact Logic.axiomB
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicENTDB

end
