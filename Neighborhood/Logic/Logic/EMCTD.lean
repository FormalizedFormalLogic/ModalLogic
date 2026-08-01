module

public import Neighborhood.Logic.Logic.EMCT

@[expose] public section

variable {α : Type u}

namespace LogicEMCTD

/-- The axiom scheme `D` is redundant over `M`, `C`, and `T`. -/
theorem eq_LogicEMCT : (@LogicEMCTD α) = LogicEMCT := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomT | exact Logic.axiomD
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicEMCTD

end
