module

public import Neighborhood.Logic.Logic.ECB
public import Neighborhood.Logic.Logic.EMB
public import Neighborhood.Logic.Logic.EMC

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMCB

/-- The axiom scheme `C` is redundant over `M` and `B`. -/
theorem eq_LogicEMB : (@LogicEMCB α) = LogicEMB := by
  hilbert_eq_axioms

instance : (@LogicEMCB α).IsConsistent := by
  rw [eq_LogicEMB]; infer_instance

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMCB α) := by
  rw [eq_LogicEMB]; exact LogicEMB.not_provable_axiomT a

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEMCB α) := by
  rw [eq_LogicEMB]; exact LogicEMB.not_provable_axiomD a

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEMCB α) := by
  rw [eq_LogicEMB]; exact LogicEMB.not_provable_axiomP

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMCB α) := by
  rw [eq_LogicEMB]; exact LogicEMB.not_provable_axiomFour a

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMCB α) := by
  rw [eq_LogicEMB]; exact LogicEMB.not_provable_axiomFive a

end LogicEMCB

end
