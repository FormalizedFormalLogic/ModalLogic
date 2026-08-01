module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

/-- The axiom `N` is redundant over `M`, `C` and `5`. -/
theorem LogicEMCN5.eq_LogicEMC5 : (@LogicEMCN5 α) = LogicEMC5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | rfl) | ⟨B, rfl⟩) <;>
      first
        | exact Logic.axiomM
        | exact Logic.axiomC
        | exact Logic.axiomFive
        | exact Logic.axiomN
  · exact Hilbert.subset_of_subset_axioms (by grind)

end
