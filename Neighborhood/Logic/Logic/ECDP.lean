module

public import Neighborhood.Logic.Logic.ECP

@[expose] public section

variable {α : Type u}

namespace LogicECDP

/-- The axiom scheme `D` is redundant over `C` and `P`. -/
theorem eq_LogicECP : (@LogicECDP α) = LogicECP := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, rfl⟩) | rfl) <;>
      first | exact Logic.axiomC | exact Logic.axiomD | exact Logic.axiomP
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicECDP

end
