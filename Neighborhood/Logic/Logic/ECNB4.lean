module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

/-- The axiom `N` is redundant over `B` and `4`. -/
theorem LogicECNB4.eq_LogicECB4 : (@LogicECNB4 α) = LogicECB4 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomB | exact Logic.axiomFour
  · exact Hilbert.subset_of_subset_axioms (by grind)

end
