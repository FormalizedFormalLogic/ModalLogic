module

public import Neighborhood.Hilbert.Logics
public import Neighborhood.Logic.Logic.ECDB

@[expose] public section

variable {α : Type u}

namespace LogicEMCDB

/-- The axiom scheme `C` is redundant over `M`, `D`, and `B`. -/
theorem eq_LogicEMDB : (@LogicEMCDB α) = LogicEMDB := by
  hilbert_eq_axioms

theorem ssubset_LogicECDB : @LogicECDB ℕ ⊂ LogicEMCDB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicECDB.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, ProvableHilbert.axm (by grind), hA⟩

end LogicEMCDB

end
