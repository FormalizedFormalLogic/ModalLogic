module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

/-- The axiom `N` is redundant over `M`, `4`, and `5`. -/
theorem LogicEMND45.eq_LogicEMD45 : (@LogicEMND45 α) = LogicEMD45 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first
        | exact Logic.axiomM
        | exact Logic.axiomN
        | exact Logic.axiomD
        | exact Logic.axiomFour
        | exact Logic.axiomFive
  · exact Hilbert.subset_of_subset_axioms (by grind)

end
