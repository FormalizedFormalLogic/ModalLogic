module

public import Neighborhood.Logic.Logic.EMCNTDB45

@[expose] public section

variable {α : Type u}

namespace LogicEMCTDB45

/-- The axiom `N` is redundant over `M`, `C`, `T`, `D`, `B`, `4`, `5`. -/
theorem eq_LogicEMCNTDB45 : (@LogicEMCTDB45 α) = LogicEMCNTDB45 := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind (instances := 20000))
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((((((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) |
      ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomT |
        exact Logic.axiomD | exact Logic.axiomB | exact Logic.axiomFour | exact Logic.axiomFive

instance : (@LogicEMCTDB45 α).IsConsistent := by
  rw [eq_LogicEMCNTDB45]; infer_instance

end LogicEMCTDB45

end
