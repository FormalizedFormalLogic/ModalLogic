module

public import Neighborhood.Logic.Logic.EMT5
public import Neighborhood.Logic.Logic.EMNT4

@[expose] public section

variable {α : Type u}

namespace LogicEMNTB4

/-- Over `M`, `T`, and `5`, the axiom schemes `N`, `B`, and `4` axiomatise the same logic. -/
theorem eq_LogicEMT5 : (@LogicEMNTB4 α) = LogicEMT5 := by
  hilbert_eq_axioms

theorem ssubset_LogicEMNT4 : @LogicEMNT4 ℕ ⊂ LogicEMNTB4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEMNT4.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, ProvableHilbert.axm (by grind), hA⟩

end LogicEMNTB4

end
