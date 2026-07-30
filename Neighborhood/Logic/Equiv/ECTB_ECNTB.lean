module

public import Neighborhood.Hilbert.Logics

/-! # `ECTB` and `ECNTB` are the same logic -/

@[expose] public section

variable {α : Type u}

/-- The axiom `N` is redundant over `T` and `B`. -/
theorem LogicECTB_eq_LogicECNTB : (@LogicECTB α) = LogicECNTB := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomT | exact Logic.axiomB

end
