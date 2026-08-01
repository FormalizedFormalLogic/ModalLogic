module

public import Neighborhood.Logic.Logic.ECT

@[expose] public section

variable {α : Type u}

namespace LogicECTP

/-- The axiom `P` is redundant over `C` and `T`. -/
theorem eq_LogicECT : (@LogicECTP α) = LogicECT := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, rfl⟩) | rfl) <;>
      first | exact Logic.axiomC | exact Logic.axiomP | exact Logic.axiomT
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicECTP

end
