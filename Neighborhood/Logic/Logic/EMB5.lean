module

public import Neighborhood.Logic.Logic.EMB4
public import Neighborhood.Logic.Logic.EB5

@[expose] public section

variable {α : Type u}

namespace LogicEMB5

/-- Over `EMB`, the axiom scheme `5` and the axiom scheme `4` axiomatise the same logic. -/
theorem eq_LogicEMB4 : (@LogicEMB5 α) = LogicEMB4 := by
  hilbert_eq_axioms

theorem ssubset_LogicEB5 : @LogicEB5 ℕ ⊂ LogicEMB5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicEB5.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, ProvableHilbert.axm (by grind), hA⟩

end LogicEMB5

end
