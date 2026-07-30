module

public import Neighborhood.Hilbert.Logics

/-! # `EMB`, `EMCB`, `EMNB`, and `EMCNB` are all the same logic -/

@[expose] public section

variable {α : Type u}

/-- The axiom scheme `C` is redundant over `M` and `B`. -/
theorem LogicEMB_eq_LogicEMCB : (@LogicEMB α) = LogicEMCB := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomB

/-- The axiom `N` is redundant over `M` and `B`. -/
theorem LogicEMB_eq_LogicEMNB : (@LogicEMB α) = LogicEMNB := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomN | exact Logic.axiomB

/-- The axiom scheme `C` and the axiom `N` are both redundant over `M` and `B`. -/
theorem LogicEMB_eq_LogicEMCNB : (@LogicEMB α) = LogicEMCNB := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | rfl) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomB

/-- `EMCB` and `EMNB` are the same logic. -/
theorem LogicEMCB_eq_LogicEMNB : (@LogicEMCB α) = LogicEMNB :=
  LogicEMB_eq_LogicEMCB.symm.trans LogicEMB_eq_LogicEMNB

/-- `EMCB` and `EMCNB` are the same logic. -/
theorem LogicEMCB_eq_LogicEMCNB : (@LogicEMCB α) = LogicEMCNB :=
  LogicEMB_eq_LogicEMCB.symm.trans LogicEMB_eq_LogicEMCNB

/-- `EMNB` and `EMCNB` are the same logic. -/
theorem LogicEMNB_eq_LogicEMCNB : (@LogicEMNB α) = LogicEMCNB :=
  LogicEMB_eq_LogicEMNB.symm.trans LogicEMB_eq_LogicEMCNB

end
