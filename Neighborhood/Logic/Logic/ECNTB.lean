module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

/-- The axiom `N` is redundant over `T` and `B`. -/
theorem LogicECNTB.eq_LogicECTB : (@LogicECNTB α) = LogicECTB := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomT | exact Logic.axiomB
  · exact Hilbert.subset_of_subset_axioms (by grind)

end
