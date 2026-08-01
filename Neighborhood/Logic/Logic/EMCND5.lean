module

public import Neighborhood.Hilbert.Logics
public import Neighborhood.Logic.Logic.ECND5

@[expose] public section

variable {α : Type u}

namespace LogicEMCND5

/-- The axiom `N` is redundant over `M`, `C`, and `5`. -/
theorem eq_LogicEMCD5 : (@LogicEMCND5 α) = LogicEMCD5 := by
  hilbert_eq_axioms

theorem ssubset_LogicECND5 : @LogicECND5 ℕ ⊂ LogicEMCND5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicECND5.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, ProvableHilbert.axm (by grind), hA⟩

end LogicEMCND5

end
