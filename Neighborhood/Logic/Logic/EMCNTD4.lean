module

public import Neighborhood.Logic.Logic.EMCNT4

@[expose] public section

variable {α : Type u}

namespace LogicEMCNTD4

/-- The axiom `D` is redundant over `M`, `C`, `N`, `T`, `4`. -/
theorem eq_LogicEMCNT4 : (@LogicEMCNTD4 α) = LogicEMCNT4 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomT |
        exact Logic.axiomD | exact Logic.axiomFour
  · exact Hilbert.subset_of_subset_axioms (by grind (instances := 20000))

instance : (@LogicEMCNTD4 α).IsConsistent := by
  rw [eq_LogicEMCNT4]; infer_instance

end LogicEMCNTD4

end
