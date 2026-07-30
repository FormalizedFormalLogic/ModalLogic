module

public import Neighborhood.Hilbert.Logics

/-! # `EMTB`, `EMCTB`, `EMNTB`, and `EMCNTB` are all the same logic -/

@[expose] public section

variable {α : Type u}

/-- The axiom scheme `C` is redundant over `M`, `T`, and `B`. -/
theorem LogicEMTB_eq_LogicEMCTB : (@LogicEMTB α) = LogicEMCTB := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomT | exact Logic.axiomB

/-- The axiom `N` is redundant over `T` and `B`. -/
theorem LogicEMTB_eq_LogicEMNTB : (@LogicEMTB α) = LogicEMNTB := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomN | exact Logic.axiomT | exact Logic.axiomB

/-- The axiom scheme `C` is redundant over `M`, `T`, and `B`, and the axiom `N` is redundant
over `T` and `B`. -/
theorem LogicEMTB_eq_LogicEMCNTB : (@LogicEMTB α) = LogicEMCNTB := by
  apply Set.Subset.antisymm
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first
        | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomT
        | exact Logic.axiomB

/-- `EMTB`, `EMCTB`, `EMNTB`, and `EMCNTB` are all the same logic. -/
theorem LogicEMCTB_eq_LogicEMNTB : (@LogicEMCTB α) = LogicEMNTB :=
  LogicEMTB_eq_LogicEMCTB.symm.trans LogicEMTB_eq_LogicEMNTB

/-- `EMTB`, `EMCTB`, `EMNTB`, and `EMCNTB` are all the same logic. -/
theorem LogicEMCTB_eq_LogicEMCNTB : (@LogicEMCTB α) = LogicEMCNTB :=
  LogicEMTB_eq_LogicEMCTB.symm.trans LogicEMTB_eq_LogicEMCNTB

/-- `EMTB`, `EMCTB`, `EMNTB`, and `EMCNTB` are all the same logic. -/
theorem LogicEMNTB_eq_LogicEMCNTB : (@LogicEMNTB α) = LogicEMCNTB :=
  LogicEMTB_eq_LogicEMNTB.symm.trans LogicEMTB_eq_LogicEMCNTB

end
