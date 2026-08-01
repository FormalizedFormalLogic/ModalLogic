module

public import Neighborhood.Logic.Logic.ET5
public import Neighborhood.Logic.Logic.EN45

@[expose] public section

variable {α : Type u}

namespace LogicENT45

/-- The axiom scheme `N` is redundant over `T`, `4` and `5`. -/
theorem eq_LogicET5 : (@LogicENT45 α) = LogicET5 := by
  hilbert_eq_axioms

theorem ssubset_LogicEN45 : @LogicEN45 ℕ ⊂ LogicENT45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEN45.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, ProvableHilbert.axm (by grind), hA⟩

end LogicENT45

end
