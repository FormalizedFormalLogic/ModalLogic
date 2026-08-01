module

public import Neighborhood.Logic.Logic.EMD

@[expose] public section

variable {α : Type u}

namespace LogicEMDP

/-- The axiom `P` is redundant over `M` and `D`. -/
theorem eq_LogicEMD : (@LogicEMDP α) = LogicEMD := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, rfl⟩) | rfl) <;>
      first | exact Logic.axiomM | exact Logic.axiomD | exact Logic.axiomP
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicEMDP

end
