module

public import Neighborhood.Hilbert.Logics

/-! # `EMCD45` and `EMCND45` are the same logic -/

@[expose] public section

variable {α : Type u}

/-- The axiom `N` is redundant over `M`, `C`, `4`, and `5`. -/
theorem LogicEMCD45_eq_LogicEMCND45 : (@LogicEMCD45 α) = LogicEMCND45 := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first
        | exact Logic.axiomM
        | exact Logic.axiomC
        | exact Logic.axiomN
        | exact Logic.axiomD
        | exact Logic.axiomFour
        | exact Logic.axiomFive

end
