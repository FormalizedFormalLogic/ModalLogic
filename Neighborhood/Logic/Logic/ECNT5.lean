module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

/-- The axiom `N` is redundant over `T` and `5`. -/
theorem LogicECNT5.eq_LogicECT5 : (@LogicECNT5 α) = LogicECT5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomT | exact Logic.axiomFive
  · exact Hilbert.subset_of_subset_axioms (by grind)

end
