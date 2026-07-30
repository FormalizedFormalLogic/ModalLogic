module

public import Neighborhood.Hilbert.Logics

/-! # `ET5` and `ENT5` are the same logic -/

@[expose] public section

variable {α : Type u}

/-- The axiom `N` is redundant over `T` and `5`. -/
theorem LogicET5_eq_LogicENT5 : (@LogicET5 α) = LogicENT5 := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((rfl | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomT | exact Logic.axiomFive

end
