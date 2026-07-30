module

public import Neighborhood.Hilbert.Logics

/-! # `EMT5`, `EMCT5`, `EMNT5`, and `EMCNT5` are all the same logic -/

@[expose] public section

variable {α : Type u}

/-- The axiom scheme `C` is redundant over `M`, `T`, and `5`. -/
theorem LogicEMT5_eq_LogicEMCT5 : (@LogicEMT5 α) = LogicEMCT5 := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomT | exact Logic.axiomFive

/-- The axiom `N` is redundant over `M`, `T`, and `5`. -/
theorem LogicEMT5_eq_LogicEMNT5 : (@LogicEMT5 α) = LogicEMNT5 := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomN | exact Logic.axiomT | exact Logic.axiomFive

/-- The axiom scheme `C` and the axiom `N` are redundant over `M`, `T`, and `5`. -/
theorem LogicEMT5_eq_LogicEMCNT5 : (@LogicEMT5 α) = LogicEMCNT5 := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first
        | exact Logic.axiomM
        | exact Logic.axiomC
        | exact Logic.axiomN
        | exact Logic.axiomT
        | exact Logic.axiomFive

/-- `EMCT5` and `EMNT5` are the same logic. -/
theorem LogicEMCT5_eq_LogicEMNT5 : (@LogicEMCT5 α) = LogicEMNT5 :=
  LogicEMT5_eq_LogicEMCT5.symm.trans LogicEMT5_eq_LogicEMNT5

/-- `EMCT5` and `EMCNT5` are the same logic. -/
theorem LogicEMCT5_eq_LogicEMCNT5 : (@LogicEMCT5 α) = LogicEMCNT5 :=
  LogicEMT5_eq_LogicEMCT5.symm.trans LogicEMT5_eq_LogicEMCNT5

/-- `EMNT5` and `EMCNT5` are the same logic. -/
theorem LogicEMNT5_eq_LogicEMCNT5 : (@LogicEMNT5 α) = LogicEMCNT5 :=
  LogicEMT5_eq_LogicEMNT5.symm.trans LogicEMT5_eq_LogicEMCNT5

end
