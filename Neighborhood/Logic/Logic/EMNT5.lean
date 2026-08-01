module

public import Neighborhood.Hilbert.Logics
public import Neighborhood.Logic.Logic.EMCT5

@[expose] public section

variable {α : Type u}

/-- The axiom `N` is redundant over `M`, `T`, and `5`. -/
theorem LogicEMNT5.eq_LogicEMT5 : (@LogicEMNT5 α) = LogicEMT5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomN | exact Logic.axiomT | exact Logic.axiomFive
  · exact Hilbert.subset_of_subset_axioms (by grind)

/-- `EMCT5` and `EMNT5` are the same logic. -/
theorem LogicEMNT5.eq_LogicEMCT5 : (@LogicEMNT5 α) = LogicEMCT5 :=
  LogicEMNT5.eq_LogicEMT5.trans LogicEMCT5.eq_LogicEMT5.symm

end
