module

public import Neighborhood.Hilbert.Logics

@[expose] public section

variable {α : Type u}

/-- Over `ECN`, the axiom `P` and the axiom scheme `D` axiomatise the same logic. -/
theorem LogicECNP_eq_LogicECND : (@LogicECNP α) = LogicECND := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | rfl) | rfl) <;>
      first | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomP_of_ND
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomD

end
