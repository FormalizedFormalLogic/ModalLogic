module

public import Neighborhood.Hilbert.Logics
public import Neighborhood.Logic.Logic.EMCDB
public import Neighborhood.Logic.Logic.EMNDB

@[expose] public section

variable {α : Type u}

/-- The axiom scheme `C` and the axiom `N` are both redundant over `M`, `D`, and `B`. -/
theorem LogicEMCNDB.eq_LogicEMDB : (@LogicEMCNDB α) = LogicEMDB := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first
        | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN
        | exact Logic.axiomD | exact Logic.axiomB
  · exact Hilbert.subset_of_subset_axioms (by grind)

/-- `EMCDB` and `EMCNDB` are the same logic. -/
theorem LogicEMCNDB.eq_LogicEMCDB : (@LogicEMCNDB α) = LogicEMCDB :=
  LogicEMCNDB.eq_LogicEMDB.trans LogicEMCDB.eq_LogicEMDB.symm

/-- `EMNDB` and `EMCNDB` are the same logic. -/
theorem LogicEMCNDB.eq_LogicEMNDB : (@LogicEMCNDB α) = LogicEMNDB :=
  LogicEMCNDB.eq_LogicEMDB.trans LogicEMNDB.eq_LogicEMDB.symm

end
