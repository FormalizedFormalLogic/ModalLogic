module

public import Neighborhood.Logic.Logic.ECD4
public import Neighborhood.Logic.Logic.ECDB
public import Neighborhood.Logic.Logic.ECT5

@[expose] public section

variable {α : Type u}

namespace LogicECDB4

/-- Over `C`, the axiom schemes `D`, `B`, and `4` axiomatise the same logic as `T` and `5`. -/
theorem eq_LogicECT5 : (@LogicECDB4 α) = LogicECT5 := by
  hilbert_eq_axioms

theorem ssubset_LogicECD4 : @LogicECD4 ℕ ⊂ LogicECDB4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECD4.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, ProvableHilbert.axm (by grind), hA⟩

theorem ssubset_LogicECDB : @LogicECDB ℕ ⊂ LogicECDB4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECDB.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, ProvableHilbert.axm (by grind), hA⟩

end LogicECDB4

end
