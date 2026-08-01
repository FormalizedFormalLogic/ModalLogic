module

public import Neighborhood.Logic.Logic.EMC5

@[expose] public section

variable {α : Type u}

namespace LogicENK5

/-- `ENK5` and `EMC5` axiomatise the same logic: `M` and `C` are derivable from `K`, `N` and
`5`, while conversely `K` and `N` are derivable from `M`, `C` and `5`. -/
theorem eq_LogicEMC5 : (@LogicENK5 α) = LogicEMC5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((rfl | ⟨B, C, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomK | exact Logic.axiomFive
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomFive

end LogicENK5

end
