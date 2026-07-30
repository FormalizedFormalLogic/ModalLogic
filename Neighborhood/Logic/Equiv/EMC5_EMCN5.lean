module

public import Neighborhood.Hilbert.Logics

/-! # `EMC5` and `EMCN5` are the same logic -/

@[expose] public section

variable {α : Type u}

/-- The axiom `N` is redundant over `M`, `C` and `5`. -/
theorem LogicEMC5_eq_LogicEMCN5 : (@LogicEMC5 α) = LogicEMCN5 := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | rfl) | ⟨B, rfl⟩) <;>
      first
        | exact Logic.axiomM
        | exact Logic.axiomC
        | exact Logic.axiomFive
        | exact Logic.axiomN

end
