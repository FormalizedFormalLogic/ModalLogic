module

public import Neighborhood.Logic.Logic.ET5
public import Neighborhood.Logic.Logic.END5

@[expose] public section

variable {α : Type u}

namespace LogicENTD5

/-- The axiom schemes `N` and `D` are redundant over `T` and `5`. -/
theorem eq_LogicET5 : (@LogicENTD5 α) = LogicET5 := by
  hilbert_eq_axioms

theorem ssubset_LogicEND5 : @LogicEND5 ℕ ⊂ LogicENTD5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEND5.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, ProvableHilbert.axm (by grind), hA⟩

end LogicENTD5

end
