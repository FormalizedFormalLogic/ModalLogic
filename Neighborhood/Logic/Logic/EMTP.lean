module

public import Neighborhood.Logic.Logic.EMT

@[expose] public section

variable {α : Type u}

namespace LogicEMTP

/-- The axiom `P` is redundant over `M` and `T`. -/
theorem eq_LogicEMT : (@LogicEMTP α) = LogicEMT := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, rfl⟩) | rfl) <;> first | exact Logic.axiomM | exact Logic.axiomT
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicEMTP

end
