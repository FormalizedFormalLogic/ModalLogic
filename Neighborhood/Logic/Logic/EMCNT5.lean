module

public import Neighborhood.Hilbert.Logics
public import Neighborhood.Logic.Logic.EMCT5
public import Neighborhood.Logic.Logic.EMNT5

@[expose] public section

variable {α : Type u}

/-- The axiom scheme `C` and the axiom `N` are redundant over `M`, `T`, and `5`. -/
theorem LogicEMCNT5.eq_LogicEMT5 : (@LogicEMCNT5 α) = LogicEMT5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first
        | exact Logic.axiomM
        | exact Logic.axiomC
        | exact Logic.axiomN
        | exact Logic.axiomT
        | exact Logic.axiomFive
  · exact Hilbert.subset_of_subset_axioms (by grind)

/-- `EMCT5` and `EMCNT5` are the same logic. -/
theorem LogicEMCNT5.eq_LogicEMCT5 : (@LogicEMCNT5 α) = LogicEMCT5 :=
  LogicEMCNT5.eq_LogicEMT5.trans LogicEMCT5.eq_LogicEMT5.symm

/-- `EMNT5` and `EMCNT5` are the same logic. -/
theorem LogicEMCNT5.eq_LogicEMNT5 : (@LogicEMCNT5 α) = LogicEMNT5 :=
  LogicEMCNT5.eq_LogicEMT5.trans LogicEMNT5.eq_LogicEMT5.symm

end
