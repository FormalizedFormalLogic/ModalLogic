module

public import Neighborhood.Logic.Logic.ENDB

@[expose] public section

variable {α : Type u}

namespace LogicEDPB

/-- `EDPB` and `ENDB` axiomatise the same logic: `P` is derivable from `D` and `N`, while
conversely `N` is derivable from `P` and `B`. -/
theorem eq_LogicENDB : (@LogicEDPB α) = LogicENDB := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, rfl⟩ | rfl) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomD | exact Logic.axiomP | exact Logic.axiomB
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((rfl | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomD | exact Logic.axiomB

end LogicEDPB

end
