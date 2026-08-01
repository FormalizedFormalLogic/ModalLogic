module

public import Neighborhood.Logic.Logic.EMDB

@[expose] public section

variable {α : Type u}

namespace LogicEKPB

/-- `EKPB` and `EMDB` axiomatise the same logic: `M` and `D` are derivable from `K`, `P` and `B`,
while conversely `K` and `P` are derivable from `M`, `D` and `B`. -/
theorem eq_LogicEMDB : (@LogicEKPB α) = LogicEMDB := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomK | exact Logic.axiomP | exact Logic.axiomB
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomD | exact Logic.axiomB

end LogicEKPB

end
