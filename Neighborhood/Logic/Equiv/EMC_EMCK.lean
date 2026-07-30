module

public import Neighborhood.Hilbert.Logics

/-! # `EMC` and `EMCK` are the same logic -/

@[expose] public section

variable {α : Type u}

/-- The axiom scheme `K` is redundant over `M` and `C`. -/
theorem LogicEMC_eq_LogicEMCK : (@LogicEMC α) = LogicEMCK := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | ⟨B, C, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomK_of_MC

end
