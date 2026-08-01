module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

/-- The axiom scheme `C` is redundant over `M`, `T`, and `5`. -/
theorem LogicEMCT5.eq_LogicEMT5 : (@LogicEMCT5 α) = LogicEMT5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomT | exact Logic.axiomFive
  · exact Hilbert.subset_of_subset_axioms (by grind)

end
