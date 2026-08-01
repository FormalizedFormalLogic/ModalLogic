module

public import Neighborhood.Logic.Logic.ECND4
public import Neighborhood.Logic.Logic.ECNT4

@[expose] public section

variable {α : Type u}

namespace LogicECNTD4

/-- The axiom scheme `D` is redundant over `C`, `N`, `T`, and `4`. -/
theorem eq_LogicECNT4 : (@LogicECNTD4 α) = LogicECNT4 := by
  hilbert_eq_axioms

theorem ssubset_LogicECND4 : @LogicECND4 ℕ ⊂ LogicECNTD4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECND4.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, ProvableHilbert.axm (by grind), hA⟩

end LogicECNTD4

end
