module

public import Neighborhood.Logic.Logic.EMNT

@[expose] public section

variable {α : Type u}

namespace LogicEMNTD

/-- The axiom scheme `D` is redundant over `M`, `N` and `T`. -/
theorem eq_LogicEMNT : (@LogicEMNTD α) = LogicEMNT := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomN | exact Logic.axiomT | exact Logic.axiomD
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicEMNTD

end
