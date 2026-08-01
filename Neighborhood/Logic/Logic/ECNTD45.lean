module

public import Neighborhood.Logic.Logic.ECND45
public import Neighborhood.Logic.Logic.ECNTDB45

@[expose] public section

variable {α : Type u}

namespace LogicECNTD45

/-- The axiom `B` is redundant over `C`, `N`, `T`, `D`, `4`, `5`. -/
theorem eq_LogicECNTDB45 : (@LogicECNTD45 α) = LogicECNTDB45 := by
  hilbert_eq_axioms

instance : (@LogicECNTD45 α).IsConsistent := by
  rw [eq_LogicECNTDB45]; infer_instance

theorem ssubset_LogicECND45 : @LogicECND45 ℕ ⊂ LogicECNTD45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECND45.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, ProvableHilbert.axm (by grind), hA⟩

end LogicECNTD45

end
