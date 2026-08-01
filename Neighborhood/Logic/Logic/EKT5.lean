module

public import Neighborhood.Logic.Logic.EKT
public import Neighborhood.Logic.Logic.EK5
public import Neighborhood.Logic.Logic.ET5
public import Neighborhood.Logic.Logic.EMT5

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEKT5

/-- `EKT5` and `EMT5` axiomatise the same logic: `M` is derivable from `K`, `T` and `5`, while
conversely `K` is derivable from `M`, `T` and `5`. -/
theorem eq_LogicEMT5 : (@LogicEKT5 α) = LogicEMT5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomK | exact Logic.axiomT | exact Logic.axiomFive
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomT | exact Logic.axiomFive

instance : (@LogicEKT5 α).IsConsistent := by
  rw [eq_LogicEMT5]; infer_instance

end LogicEKT5

end
