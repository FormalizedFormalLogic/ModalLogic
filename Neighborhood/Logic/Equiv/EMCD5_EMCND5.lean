module

public import Neighborhood.Hilbert.Logics

/-! # `EMCD5` and `EMCND5` are the same logic -/

@[expose] public section

variable {α : Type u}

/-- The axiom `N` is redundant over `M`, `C`, and `5`. -/
theorem LogicEMCD5_eq_LogicEMCND5 : (@LogicEMCD5 α) = LogicEMCND5 := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first
        | exact Logic.axiomM
        | exact Logic.axiomC
        | exact Logic.axiomN
        | exact Logic.axiomD
        | exact Logic.axiomFive

end
