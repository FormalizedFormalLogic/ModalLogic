module

public import Neighborhood.Logic.Logic.EMCN

@[expose] public section

variable {α : Type u}

namespace LogicEMNK

/-- The axiom scheme `C` is derivable from `M`, `N` and the axiom scheme `K`. -/
theorem eq_LogicEMCN : (@LogicEMNK α) = LogicEMCN := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | rfl) | ⟨B, C, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomN | exact Logic.axiomK
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | rfl) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN

end LogicEMNK

end
