module

public import Neighborhood.Hilbert.Logics
public import Neighborhood.Logic.Logic.EMCB4
public import Neighborhood.Logic.Logic.EMNB4

@[expose] public section

variable {α : Type u}

/-- The axiom scheme `C` and the axiom `N` are both redundant over `M`, `B`, and `4`. -/
theorem LogicEMCNB4.eq_LogicEMB4 : (@LogicEMCNB4 α) = LogicEMB4 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first
        | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomB
        | exact Logic.axiomFour
  · exact Hilbert.subset_of_subset_axioms (by grind)

/-- `EMB4`, `EMCB4`, `EMNB4`, and `EMCNB4` are all the same logic. -/
theorem LogicEMCNB4.eq_LogicEMCB4 : (@LogicEMCNB4 α) = LogicEMCB4 :=
  LogicEMCNB4.eq_LogicEMB4.trans LogicEMCB4.eq_LogicEMB4.symm

/-- `EMB4`, `EMCB4`, `EMNB4`, and `EMCNB4` are all the same logic. -/
theorem LogicEMCNB4.eq_LogicEMNB4 : (@LogicEMCNB4 α) = LogicEMNB4 :=
  LogicEMCNB4.eq_LogicEMB4.trans LogicEMNB4.eq_LogicEMB4.symm

end
