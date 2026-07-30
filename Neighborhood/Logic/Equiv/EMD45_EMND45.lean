module

public import Neighborhood.Hilbert.Logics

/-! # `EMD45` and `EMND45` are the same logic -/

@[expose] public section

variable {α : Type u}

/-- The axiom `N` is redundant over `M`, `4`, and `5`. -/
theorem LogicEMD45_eq_LogicEMND45 : (@LogicEMD45 α) = LogicEMND45 := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first
        | exact Logic.axiomM
        | exact Logic.axiomN
        | exact Logic.axiomD
        | exact Logic.axiomFour
        | exact Logic.axiomFive

end
