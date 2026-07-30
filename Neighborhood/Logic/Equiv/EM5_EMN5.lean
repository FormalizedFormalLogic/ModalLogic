module

public import Neighborhood.Hilbert.Logics

/-! # `EM5` and `EMN5` are the same logic -/

@[expose] public section

variable {α : Type u}

/-- The axiom `N` is redundant over `M` and `5`. -/
theorem LogicEM5_eq_LogicEMN5 : (@LogicEM5 α) = LogicEMN5 := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomFive | exact Logic.axiomN

end
