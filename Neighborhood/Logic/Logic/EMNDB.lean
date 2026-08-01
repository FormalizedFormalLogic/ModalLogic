module

public import Neighborhood.Hilbert.Logics
public import Neighborhood.Logic.Logic.EMCDB

@[expose] public section

variable {α : Type u}

/-- The axiom `N` is redundant over `M`, `D`, and `B`. -/
theorem LogicEMNDB.eq_LogicEMDB : (@LogicEMNDB α) = LogicEMDB := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomN | exact Logic.axiomD | exact Logic.axiomB
  · exact Hilbert.subset_of_subset_axioms (by grind)

/-- `EMCDB` and `EMNDB` are the same logic. -/
theorem LogicEMNDB.eq_LogicEMCDB : (@LogicEMNDB α) = LogicEMCDB :=
  LogicEMNDB.eq_LogicEMDB.trans LogicEMCDB.eq_LogicEMDB.symm

end
