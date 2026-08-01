module

public import Neighborhood.Hilbert.Logics
public import Neighborhood.Logic.Logic.ENDB

@[expose] public section

variable {α : Type u}

namespace LogicEMNDB

/-- The axiom `N` is redundant over `M`, `D`, and `B`. -/
theorem eq_LogicEMDB : (@LogicEMNDB α) = LogicEMDB := by
  hilbert_eq_axioms

theorem ssubset_LogicENDB : @LogicENDB ℕ ⊂ LogicEMNDB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicENDB.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, ProvableHilbert.axm (by grind), hA⟩

end LogicEMNDB

end
