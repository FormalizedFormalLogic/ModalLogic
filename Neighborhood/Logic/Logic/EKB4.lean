module

public import Neighborhood.Logic.Logic.EMB4

@[expose] public section

variable {α : Type u}

namespace LogicEKB4

/-- `EKB4` and `EMB4` axiomatise the same logic: `M` is derivable from `K`, `B` and `4`, while
conversely `K` is derivable from `M`, `B` and `4`. -/
theorem eq_LogicEMB4 : (@LogicEKB4 α) = LogicEMB4 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomK | exact Logic.axiomB | exact Logic.axiomFour
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomB | exact Logic.axiomFour

end LogicEKB4

end
