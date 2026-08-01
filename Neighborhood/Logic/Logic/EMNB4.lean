module

public import Neighborhood.Hilbert.Logics
public import Neighborhood.Logic.Logic.EMCB4

@[expose] public section

variable {α : Type u}

/-- The axiom `N` is redundant over `M`, `B`, and `4`. -/
theorem LogicEMNB4.eq_LogicEMB4 : (@LogicEMNB4 α) = LogicEMB4 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomN | exact Logic.axiomB | exact Logic.axiomFour
  · exact Hilbert.subset_of_subset_axioms (by grind)

/-- `EMB4`, `EMCB4`, `EMNB4`, and `EMCNB4` are all the same logic. -/
theorem LogicEMNB4.eq_LogicEMCB4 : (@LogicEMNB4 α) = LogicEMCB4 :=
  LogicEMNB4.eq_LogicEMB4.trans LogicEMCB4.eq_LogicEMB4.symm

end
