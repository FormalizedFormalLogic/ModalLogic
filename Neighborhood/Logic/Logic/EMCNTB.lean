module

public import Neighborhood.Hilbert.Logics
public import Neighborhood.Logic.Logic.EMCTB
public import Neighborhood.Logic.Logic.EMNTB

@[expose] public section

variable {α : Type u}

/-- The axiom scheme `C` is redundant over `M`, `T`, and `B`, and the axiom `N` is redundant
over `T` and `B`. -/
theorem LogicEMCNTB.eq_LogicEMTB : (@LogicEMCNTB α) = LogicEMTB := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | rfl) | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first
        | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomT
        | exact Logic.axiomB
  · exact Hilbert.subset_of_subset_axioms (by grind)

/-- `EMTB`, `EMCTB`, `EMNTB`, and `EMCNTB` are all the same logic. -/
theorem LogicEMCNTB.eq_LogicEMCTB : (@LogicEMCNTB α) = LogicEMCTB :=
  LogicEMCNTB.eq_LogicEMTB.trans LogicEMCTB.eq_LogicEMTB.symm

/-- `EMTB`, `EMCTB`, `EMNTB`, and `EMCNTB` are all the same logic. -/
theorem LogicEMCNTB.eq_LogicEMNTB : (@LogicEMCNTB α) = LogicEMNTB :=
  LogicEMCNTB.eq_LogicEMTB.trans LogicEMNTB.eq_LogicEMTB.symm

end
