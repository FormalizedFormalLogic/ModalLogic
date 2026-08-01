module

public import Neighborhood.Logic.Logic.EDB5
public import Neighborhood.Logic.Logic.ENB5
public import Neighborhood.Logic.Logic.END5
public import Neighborhood.Logic.Logic.ENDB

@[expose] public section

variable {α : Type u}

namespace LogicENDB5

/-- The axiom scheme `N` is redundant over `D`, `B`, and `5`. -/
theorem eq_LogicEDB5 : (@LogicENDB5 α) = LogicEDB5 := by
  hilbert_eq_axioms

theorem ssubset_LogicENB5 : @LogicENB5 ℕ ⊂ LogicENDB5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicENB5.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, ProvableHilbert.axm (by grind), hA⟩

theorem ssubset_LogicEND5 : @LogicEND5 ℕ ⊂ LogicENDB5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEND5.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, ProvableHilbert.axm (by grind), hA⟩

theorem ssubset_LogicENDB : @LogicENDB ℕ ⊂ LogicENDB5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicENDB.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, ProvableHilbert.axm (by grind), hA⟩

end LogicENDB5

end
