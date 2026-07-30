module

public import Neighborhood.Hilbert.Logics

/-! # `ETB` and `ENTB` are the same logic -/

@[expose] public section

variable {α : Type u}

/-- The axiom `N` is redundant over `T` and `B`. -/
theorem LogicETB_eq_LogicENTB : (@LogicETB α) = LogicENTB := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((rfl | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomT | exact Logic.axiomB

end
