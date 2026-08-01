module

public import Neighborhood.Logic.Logic.ECNT

@[expose] public section

variable {α : Type u}

namespace LogicECNTD

/-- The axiom scheme `D` is redundant over `C`, `N` and `T`. -/
theorem eq_LogicECNT : (@LogicECNTD α) = LogicECNT := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomT | exact Logic.axiomD
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicECNTD

end
