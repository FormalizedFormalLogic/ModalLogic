module

public import Neighborhood.Hilbert.Logics

/-! # `EMC45` and `EMCN45` are the same logic -/

@[expose] public section

variable {α : Type u}

/-- The axiom `N` is redundant over `M`, `C`, `4`, and `5`. -/
theorem LogicEMC45_eq_LogicEMCN45 : (@LogicEMC45 α) = LogicEMCN45 := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first
        | exact Logic.axiomM
        | exact Logic.axiomC
        | exact Logic.axiomN
        | exact Logic.axiomFour
        | exact Logic.axiomFive

end
