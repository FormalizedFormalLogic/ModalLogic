module

public import Neighborhood.Logic.Logic.ECTB

@[expose] public section

variable {α : Type u}

namespace LogicECTDB

/-- The axiom scheme `D` is redundant over `C`, `T` and `B`. -/
theorem eq_LogicECTB : (@LogicECTDB α) = LogicECTB := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomC | exact Logic.axiomT | exact Logic.axiomD | exact Logic.axiomB
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicECTDB

end
