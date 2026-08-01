module

public import Neighborhood.Hilbert.Logics
public import Neighborhood.Logic.Logic.ECND45

@[expose] public section

variable {α : Type u}

namespace LogicEMCND45

/-- The axiom `N` is redundant over `M`, `C`, `4`, and `5`. -/
theorem eq_LogicEMCD45 : (@LogicEMCND45 α) = LogicEMCD45 := by
  hilbert_eq_axioms

theorem ssubset_LogicECND45 : @LogicECND45 ℕ ⊂ LogicEMCND45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicECND45.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, ProvableHilbert.axm (by simp), hA⟩

end LogicEMCND45

end
