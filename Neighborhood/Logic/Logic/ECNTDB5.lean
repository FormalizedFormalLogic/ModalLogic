module

public import Neighborhood.Logic.Logic.ECNTDB45

@[expose] public section

variable {α : Type u}

namespace LogicECNTDB5

/-- The axiom `4` is redundant over `C`, `N`, `T`, `D`, `B`, `5`. -/
theorem eq_LogicECNTDB45 : (@LogicECNTDB5 α) = LogicECNTDB45 := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind (instances := 20000))
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((((((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) |
      ⟨_, rfl⟩) <;>
      first | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomT | exact Logic.axiomD |
        exact Logic.axiomB | exact Logic.axiomFour | exact Logic.axiomFive

instance : (@LogicECNTDB5 α).IsConsistent := by
  rw [eq_LogicECNTDB45]; infer_instance

end LogicECNTDB5

end
