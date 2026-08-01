module

public import Neighborhood.Logic.Logic.EMTB

@[expose] public section

variable {α : Type u}

namespace LogicEMCNTDB

/-- The axioms `C`, `N`, `D` are redundant over `M`, `T`, `B`. -/
theorem eq_LogicEMTB : (@LogicEMCNTDB α) = LogicEMTB := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomT |
        exact Logic.axiomD | exact Logic.axiomB
  · exact Hilbert.subset_of_subset_axioms (by grind (instances := 4000))

instance : (@LogicEMCNTDB α).IsConsistent := by
  rw [eq_LogicEMTB]; infer_instance

end LogicEMCNTDB

end
