module

public import Neighborhood.Logic.Logic.EB45
public import Neighborhood.Logic.Logic.EN45
public import Neighborhood.Logic.Logic.ENB5

@[expose] public section

variable {α : Type u}

namespace LogicENB45

/-- The axiom `N` is redundant over `B`, `4` and `5`. -/
theorem eq_LogicEB45 : (@LogicENB45 α) = LogicEB45 := by
  hilbert_eq_axioms

theorem ssubset_LogicEN45 : @LogicEN45 ℕ ⊂ LogicENB45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEN45.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, ProvableHilbert.axm (by grind), hA⟩

theorem ssubset_LogicENB5 : @LogicENB5 ℕ ⊂ LogicENB45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicENB5.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, ProvableHilbert.axm (by grind), hA⟩

end LogicENB45

end
