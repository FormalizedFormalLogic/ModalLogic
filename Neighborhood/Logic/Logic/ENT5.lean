module

public import Neighborhood.Logic.Logic.ET5
public import Neighborhood.Logic.Logic.EN5
public import Neighborhood.Logic.Logic.ENT

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicENT5

/-- The axiom `N` is redundant over `T` and `5`. -/
theorem eq_LogicET5 : (@LogicENT5 α) = LogicET5 := by
  hilbert_eq_axioms

instance : (@LogicENT5 α).IsConsistent := by
  rw [eq_LogicET5]; infer_instance

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicENT5 α) := by
  rw [eq_LogicET5]; exact LogicET5.not_provable_axiomK a b hab

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicENT5 α) := by
  rw [eq_LogicET5]; exact LogicET5.not_provable_axiomM a b hab

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicENT5 α) := by
  rw [eq_LogicET5]; exact LogicET5.not_provable_axiomC a b hab

end LogicENT5

end
