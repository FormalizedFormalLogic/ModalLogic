module

public import Neighborhood.Logic.Logic.ECT

@[expose] public section

variable {α : Type u}

namespace LogicECTD

/-- The axiom scheme `D` is redundant over `C` and `T`. -/
theorem eq_LogicECT : (@LogicECTD α) = LogicECT := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomC | exact Logic.axiomT | exact Logic.axiomD
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicECTD

end
