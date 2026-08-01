module

public import Neighborhood.Hilbert.Logics
public import Neighborhood.Logic.Logic.EMCB
public import Neighborhood.Logic.Logic.EMNB

@[expose] public section

variable {α : Type u}

/-- The axiom scheme `C` and the axiom `N` are both redundant over `M` and `B`. -/
theorem LogicEMCNB.eq_LogicEMB : (@LogicEMCNB α) = LogicEMB := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | rfl) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomB
  · exact Hilbert.subset_of_subset_axioms (by grind)

/-- `EMCB` and `EMCNB` are the same logic. -/
theorem LogicEMCNB.eq_LogicEMCB : (@LogicEMCNB α) = LogicEMCB :=
  LogicEMCNB.eq_LogicEMB.trans LogicEMCB.eq_LogicEMB.symm

/-- `EMNB` and `EMCNB` are the same logic. -/
theorem LogicEMCNB.eq_LogicEMNB : (@LogicEMCNB α) = LogicEMNB :=
  LogicEMCNB.eq_LogicEMB.trans LogicEMNB.eq_LogicEMB.symm

end
