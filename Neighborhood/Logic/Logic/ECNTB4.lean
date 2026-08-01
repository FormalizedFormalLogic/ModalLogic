module

public import Neighborhood.Logic.Logic.ECNT4
public import Neighborhood.Logic.Logic.ECT5

@[expose] public section

variable {α : Type u}

namespace LogicECNTB4

/-- Over `C`, the axiom schemes `N`, `T`, `B` and `4` axiomatise the same logic
as `T` and `5`. -/
theorem eq_LogicECT5 : (@LogicECNTB4 α) = LogicECT5 := by
  hilbert_eq_axioms

theorem ssubset_LogicECNT4 : @LogicECNT4 ℕ ⊂ LogicECNTB4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECNT4.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, ProvableHilbert.axm (by grind), hA⟩

end LogicECNTB4

end
