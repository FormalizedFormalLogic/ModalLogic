module

public import Neighborhood.Logic.Logic.EMTB

@[expose] public section

variable {α : Type u}

namespace LogicEKTB

/-- `EKTB` and `EMTB` axiomatise the same logic: `M` is derivable from `K`, `T` and `B`, while
conversely `K` is derivable from `M`, `T` and `B`. -/
theorem eq_LogicEMTB : (@LogicEKTB α) = LogicEMTB := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomK | exact Logic.axiomT | exact Logic.axiomB
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomT | exact Logic.axiomB

end LogicEKTB

end
