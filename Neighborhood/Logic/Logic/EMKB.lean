module

public import Neighborhood.Logic.Logic.EMB

@[expose] public section

variable {α : Type u}

namespace LogicEMKB

/-- The axiom scheme `K` is redundant over `M` and `B`. -/
theorem eq_LogicEMB : (@LogicEMKB α) = LogicEMB := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomK | exact Logic.axiomB
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicEMKB

end
