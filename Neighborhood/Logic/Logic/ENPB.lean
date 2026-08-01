module

public import Neighborhood.Logic.Logic.EPB

@[expose] public section

variable {α : Type u}

namespace LogicENPB

/-- The axiom `N` is redundant over `P` and `B`. -/
theorem eq_LogicEPB : (@LogicENPB α) = LogicEPB := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((rfl | rfl) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomP | exact Logic.axiomB
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicENPB

end
