module

public import Neighborhood.Logic.Logic.ENB5
public import Neighborhood.Logic.Logic.ET5

@[expose] public section

variable {α : Type u}

namespace LogicENTB5

/-- The axiom `N` and the axiom scheme `B` are redundant over `T` and `5`. -/
theorem eq_LogicET5 : (@LogicENTB5 α) = LogicET5 := by
  hilbert_eq_axioms

theorem ssubset_LogicENB5 : @LogicENB5 ℕ ⊂ LogicENTB5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicENB5.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, ProvableHilbert.axm (by grind), hA⟩

end LogicENTB5

end
