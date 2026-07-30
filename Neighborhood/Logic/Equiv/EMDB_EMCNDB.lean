module

public import Neighborhood.Hilbert.Logics

/-! # `EMDB`, `EMCDB`, `EMNDB`, and `EMCNDB` are all the same logic -/

@[expose] public section

variable {α : Type u}

/-- The axiom scheme `C` is redundant over `M`, `D`, and `B`. -/
theorem LogicEMDB_eq_LogicEMCDB : (@LogicEMDB α) = LogicEMCDB := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomD | exact Logic.axiomB

/-- The axiom `N` is redundant over `M`, `D`, and `B`. -/
theorem LogicEMDB_eq_LogicEMNDB : (@LogicEMDB α) = LogicEMNDB := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomN | exact Logic.axiomD | exact Logic.axiomB

/-- The axiom scheme `C` and the axiom `N` are both redundant over `M`, `D`, and `B`. -/
theorem LogicEMDB_eq_LogicEMCNDB : (@LogicEMDB α) = LogicEMCNDB := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first
        | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN
        | exact Logic.axiomD | exact Logic.axiomB

/-- `EMCDB` and `EMNDB` are the same logic. -/
theorem LogicEMCDB_eq_LogicEMNDB : (@LogicEMCDB α) = LogicEMNDB :=
  LogicEMDB_eq_LogicEMCDB.symm.trans LogicEMDB_eq_LogicEMNDB

/-- `EMCDB` and `EMCNDB` are the same logic. -/
theorem LogicEMCDB_eq_LogicEMCNDB : (@LogicEMCDB α) = LogicEMCNDB :=
  LogicEMDB_eq_LogicEMCDB.symm.trans LogicEMDB_eq_LogicEMCNDB

/-- `EMNDB` and `EMCNDB` are the same logic. -/
theorem LogicEMNDB_eq_LogicEMCNDB : (@LogicEMNDB α) = LogicEMCNDB :=
  LogicEMDB_eq_LogicEMNDB.symm.trans LogicEMDB_eq_LogicEMCNDB

end
