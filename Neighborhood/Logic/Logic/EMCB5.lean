module

public import Neighborhood.Logic.Logic.EMB4
public import Neighborhood.Logic.Logic.ECB5

@[expose] public section

variable {α : Type u}

namespace LogicEMCB5

/-- The axiom scheme `C` is redundant over `M`, `B` and `5`, and the axiom scheme `4` is derivable
over `M`, `C`, `B` and `5`. -/
theorem eq_LogicEMB4 : (@LogicEMCB5 α) = LogicEMB4 := by
  hilbert_eq_axioms

theorem ssubset_LogicECB5 : @LogicECB5 ℕ ⊂ LogicEMCB5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicECB5.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, ProvableHilbert.axm (by grind), hA⟩

end LogicEMCB5

end
