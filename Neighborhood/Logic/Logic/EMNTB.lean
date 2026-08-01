module

public import Neighborhood.Hilbert.Logics
public import Neighborhood.Logic.Logic.EMNT

@[expose] public section

variable {α : Type u}

namespace LogicEMNTB

/-- The axiom `N` is redundant over `T` and `B`. -/
theorem eq_LogicEMTB : (@LogicEMNTB α) = LogicEMTB := by
  hilbert_eq_axioms

theorem ssubset_LogicEMNT : @LogicEMNT ℕ ⊂ LogicEMNTB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEMNT.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, ProvableHilbert.axm (by grind), hA⟩

end LogicEMNTB

end
