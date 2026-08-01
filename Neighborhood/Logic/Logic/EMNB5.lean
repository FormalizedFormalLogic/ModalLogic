module

public import Neighborhood.Logic.Logic.EMB4
public import Neighborhood.Logic.Logic.ENB5

@[expose] public section

variable {α : Type u}

namespace LogicEMNB5

/-- The axiom scheme `N` is redundant over `M`, `B`, and `5`; conversely, `5` is derivable from `M`, `N`, and `B`. -/
theorem eq_LogicEMB4 : (@LogicEMNB5 α) = LogicEMB4 := by
  hilbert_eq_axioms

theorem ssubset_LogicENB5 : @LogicENB5 ℕ ⊂ LogicEMNB5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicENB5.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, ProvableHilbert.axm (by grind), hA⟩

end LogicEMNB5

end
