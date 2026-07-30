module

public import Neighborhood.Hilbert.Logics

/-! # `ECB4` and `ECNB4` are the same logic -/

@[expose] public section

variable {α : Type u}

/-- The axiom `N` is redundant over `B` and `4`. -/
theorem LogicECB4_eq_LogicECNB4 : (@LogicECB4 α) = LogicECNB4 := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomB | exact Logic.axiomFour

end
