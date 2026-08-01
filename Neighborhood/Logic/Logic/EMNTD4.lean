module

public import Neighborhood.Logic.Logic.EMNT4
public import Neighborhood.Logic.Logic.EMND4

@[expose] public section

variable {α : Type u}

namespace LogicEMNTD4

/-- The axiom scheme `D` is redundant over `M`, `N`, `T`, and `Four`. -/
theorem eq_LogicEMNT4 : (@LogicEMNTD4 α) = LogicEMNT4 := by
  hilbert_eq_axioms

theorem ssubset_LogicEMND4 : @LogicEMND4 ℕ ⊂ LogicEMNTD4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEMND4.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, ProvableHilbert.axm (by grind), hA⟩

end LogicEMNTD4

end
