module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

/-- The axiom `N` is redundant over `M` and `5`. -/
theorem LogicEMND5.eq_LogicEMD5 : (@LogicEMND5 α) = LogicEMD5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomN | exact Logic.axiomD | exact Logic.axiomFive
  · exact Hilbert.subset_of_subset_axioms (by grind)

end
