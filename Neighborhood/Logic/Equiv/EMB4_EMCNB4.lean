module

public import Neighborhood.Hilbert.Logics

/-! # `EMB4`, `EMCB4`, `EMNB4`, and `EMCNB4` are all the same logic -/

@[expose] public section

variable {α : Type u}

/-- The axiom scheme `C` is redundant over `M`, `B`, and `4`. -/
theorem LogicEMB4_eq_LogicEMCB4 : (@LogicEMB4 α) = LogicEMCB4 := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomB | exact Logic.axiomFour

/-- The axiom `N` is redundant over `M`, `B`, and `4`. -/
theorem LogicEMB4_eq_LogicEMNB4 : (@LogicEMB4 α) = LogicEMNB4 := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomN | exact Logic.axiomB | exact Logic.axiomFour

/-- The axiom scheme `C` and the axiom `N` are both redundant over `M`, `B`, and `4`. -/
theorem LogicEMB4_eq_LogicEMCNB4 : (@LogicEMB4 α) = LogicEMCNB4 := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first
        | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomB
        | exact Logic.axiomFour

/-- `EMB4`, `EMCB4`, `EMNB4`, and `EMCNB4` are all the same logic. -/
theorem LogicEMCB4_eq_LogicEMNB4 : (@LogicEMCB4 α) = LogicEMNB4 :=
  LogicEMB4_eq_LogicEMCB4.symm.trans LogicEMB4_eq_LogicEMNB4

/-- `EMB4`, `EMCB4`, `EMNB4`, and `EMCNB4` are all the same logic. -/
theorem LogicEMCB4_eq_LogicEMCNB4 : (@LogicEMCB4 α) = LogicEMCNB4 :=
  LogicEMB4_eq_LogicEMCB4.symm.trans LogicEMB4_eq_LogicEMCNB4

/-- `EMB4`, `EMCB4`, `EMNB4`, and `EMCNB4` are all the same logic. -/
theorem LogicEMNB4_eq_LogicEMCNB4 : (@LogicEMNB4 α) = LogicEMCNB4 :=
  LogicEMB4_eq_LogicEMNB4.symm.trans LogicEMB4_eq_LogicEMCNB4

end
