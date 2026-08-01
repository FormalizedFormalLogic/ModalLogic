module

public import Neighborhood.Logic.Logic.EMCN

@[expose] public section

variable {α : Type u}

namespace LogicECNK

/-- `ECNK` and `EMCN` axiomatise the same logic: `M` is derivable from `K` and `N`, while
conversely `K` is derivable from `M` and `C`. -/
theorem eq_LogicEMCN : (@LogicECNK α) = LogicEMCN := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | rfl) | ⟨B, C, rfl⟩) <;>
      first | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomK
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | rfl) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN

end LogicECNK

end
