module

public import Neighborhood.Hilbert.Logics
public import Neighborhood.Logic.Logic.ECN45

@[expose] public section

variable {α : Type u}

namespace LogicEMCN45

/-- The axiom `N` is redundant over `M`, `C`, `4`, and `5`. -/
theorem eq_LogicEMC45 : (@LogicEMCN45 α) = LogicEMC45 := by
  hilbert_eq_axioms

theorem ssubset_LogicECN45 : @LogicECN45 ℕ ⊂ LogicEMCN45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicECN45.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, ProvableHilbert.axm (by grind), hA⟩

end LogicEMCN45

end
