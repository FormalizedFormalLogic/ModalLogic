module

public import Neighborhood.Hilbert.Logics

/-! # `ECT5` and `ECNT5` are the same logic -/

@[expose] public section

variable {α : Type u}

/-- The axiom `N` is redundant over `T` and `5`. -/
theorem LogicECT5_eq_LogicECNT5 : (@LogicECT5 α) = LogicECNT5 := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomT | exact Logic.axiomFive

end
