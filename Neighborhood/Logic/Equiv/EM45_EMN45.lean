module

public import Neighborhood.Hilbert.Logics

/-! # `EM45` and `EMN45` are the same logic -/

@[expose] public section

variable {α : Type u}

/-- The axiom `N` is redundant over `M`, `4` and `5`. -/
theorem LogicEM45_eq_LogicEMN45 : (@LogicEM45 α) = LogicEMN45 := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first
        | exact Logic.axiomM
        | exact Logic.axiomFour
        | exact Logic.axiomFive
        | exact Logic.axiomN

end
