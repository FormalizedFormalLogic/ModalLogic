module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

/-- Over `EMC`, the axiom `P` and the axiom scheme `D` axiomatise the same logic. -/
theorem LogicEMCP_eq_LogicEMCD : (@LogicEMCP α) = LogicEMCD := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | rfl) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomP_of_MD
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomD

end
