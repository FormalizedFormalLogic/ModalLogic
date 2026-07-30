module

public import Neighborhood.Hilbert.Logics

/-! # `EB4` and `ENB4` are the same logic -/

@[expose] public section

variable {α : Type u}

/-- The axiom `N` is redundant over `B` and `4`. -/
theorem LogicEB4_eq_LogicENB4 : (@LogicEB4 α) = LogicENB4 := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((rfl | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomB | exact Logic.axiomFour

end
