module

public import Neighborhood.Logic.Logic.ECDB5
public import Neighborhood.Logic.Logic.ECNB5
public import Neighborhood.Logic.Logic.ECND5
public import Neighborhood.Logic.Logic.ECNDB

@[expose] public section

variable {α : Type u}

namespace LogicECNDB5

/-- The axiom scheme `N` is redundant over `C`, `D`, `B`, and `Five`. -/
theorem eq_LogicECDB5 : (@LogicECNDB5 α) = LogicECDB5 := by
  hilbert_eq_axioms

theorem ssubset_LogicECNB5 : @LogicECNB5 ℕ ⊂ LogicECNDB5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECNB5.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, ProvableHilbert.axm (by grind), hA⟩

theorem ssubset_LogicECND5 : @LogicECND5 ℕ ⊂ LogicECNDB5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECND5.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, ProvableHilbert.axm (by grind), hA⟩

theorem ssubset_LogicECNDB : @LogicECNDB ℕ ⊂ LogicECNDB5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECNDB.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, ProvableHilbert.axm (by grind), hA⟩

end LogicECNDB5

end
