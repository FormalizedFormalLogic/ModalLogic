module

public import Neighborhood.Hilbert.Logics

/-! # `EMK` and `EMCK` are the same logic -/

@[expose] public section

variable {α : Type u}

/-- The axiom scheme `C` is redundant over `M` and `K`. -/
theorem LogicEMK_eq_LogicEMCK : (@LogicEMK α) = LogicEMCK := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | ⟨B, C, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomK

end
