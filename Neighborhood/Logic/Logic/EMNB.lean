module

public import Neighborhood.Logic.Logic.ENB
public import Neighborhood.Logic.Logic.EMB
public import Neighborhood.Logic.Logic.EMN

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMNB

/-- The axiom `N` is redundant over `M` and `B`. -/
theorem eq_LogicEMB : (@LogicEMNB α) = LogicEMB := by
  hilbert_eq_axioms

instance : (@LogicEMNB α).IsConsistent := by
  rw [eq_LogicEMB]; infer_instance

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMNB α) := by
  rw [eq_LogicEMB]; exact LogicEMB.not_provable_axiomT a

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEMNB α) := by
  rw [eq_LogicEMB]; exact LogicEMB.not_provable_axiomD a

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEMNB α) := by
  rw [eq_LogicEMB]; exact LogicEMB.not_provable_axiomP

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMNB α) := by
  rw [eq_LogicEMB]; exact LogicEMB.not_provable_axiomFour a

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMNB α) := by
  rw [eq_LogicEMB]; exact LogicEMB.not_provable_axiomFive a

end LogicEMNB

end
