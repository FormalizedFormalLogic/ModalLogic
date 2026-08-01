module

public import Neighborhood.Hilbert.Logics
public import Neighborhood.Logic.Logic.EMCTB

@[expose] public section

variable {α : Type u}

/-- The axiom `N` is redundant over `T` and `B`. -/
theorem LogicEMNTB.eq_LogicEMTB : (@LogicEMNTB α) = LogicEMTB := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomN | exact Logic.axiomT | exact Logic.axiomB
  · exact Hilbert.subset_of_subset_axioms (by grind)

/-- `EMTB`, `EMCTB`, `EMNTB`, and `EMCNTB` are all the same logic. -/
theorem LogicEMNTB.eq_LogicEMCTB : (@LogicEMNTB α) = LogicEMCTB :=
  LogicEMNTB.eq_LogicEMTB.trans LogicEMCTB.eq_LogicEMTB.symm

end
