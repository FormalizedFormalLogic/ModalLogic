module

public import Neighborhood.Hilbert.Logics
public import Neighborhood.Logic.Logic.ECNDB

@[expose] public section

variable {α : Type u}

namespace LogicEMCNDB

/-- The axiom scheme `C` and the axiom `N` are both redundant over `M`, `D`, and `B`. -/
theorem eq_LogicEMDB : (@LogicEMCNDB α) = LogicEMDB := by
  hilbert_eq_axioms

theorem ssubset_LogicECNDB : @LogicECNDB ℕ ⊂ LogicEMCNDB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicECNDB.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, ProvableHilbert.axm (by grind), hA⟩

end LogicEMCNDB

end
