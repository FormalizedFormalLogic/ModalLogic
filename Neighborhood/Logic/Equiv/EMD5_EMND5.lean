module

public import Neighborhood.Hilbert.Logics

/-! # `EMD5` and `EMND5` are the same logic -/

@[expose] public section

variable {α : Type u}

/-- The axiom `N` is redundant over `M` and `5`. -/
theorem LogicEMD5_eq_LogicEMND5 : (@LogicEMD5 α) = LogicEMND5 := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomN | exact Logic.axiomD | exact Logic.axiomFive

end
