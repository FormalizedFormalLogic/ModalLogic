module

public import Neighborhood.Logic.Logic.EB4
public import Neighborhood.Logic.Logic.EN4
public import Neighborhood.Logic.Logic.ENB

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicENB4

/-- The axiom `N` is redundant over `B` and `4`. -/
theorem eq_LogicEB4 : (@LogicENB4 α) = LogicEB4 := by
  hilbert_eq_axioms

instance : (@LogicENB4 α).IsConsistent := by
  rw [eq_LogicEB4]; infer_instance

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicENB4 α) := by
  rw [eq_LogicEB4]; exact LogicEB4.not_provable_axiomK a b hab

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicENB4 α) := by
  rw [eq_LogicEB4]; exact LogicEB4.not_provable_axiomM a b hab

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicENB4 α) := by
  rw [eq_LogicEB4]; exact LogicEB4.not_provable_axiomC a b hab

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicENB4 α) := by
  rw [eq_LogicEB4]; exact LogicEB4.not_provable_axiomT a

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicENB4 α) := by
  rw [eq_LogicEB4]; exact LogicEB4.not_provable_axiomD a

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicENB4 α) := by
  rw [eq_LogicEB4]; exact LogicEB4.not_provable_axiomP

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicENB4 α) := by
  rw [eq_LogicEB4]; exact LogicEB4.not_provable_axiomFive a

end LogicENB4

end
