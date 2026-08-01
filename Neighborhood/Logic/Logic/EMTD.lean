module

public import Neighborhood.Logic.Logic.EMT

@[expose] public section

variable {α : Type u}

namespace LogicEMTD

/-- The axiom scheme `D` is redundant over `M` and `T`. -/
theorem eq_LogicEMT : (@LogicEMTD α) = LogicEMT := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomT | exact Logic.axiomD
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicEMTD

end
