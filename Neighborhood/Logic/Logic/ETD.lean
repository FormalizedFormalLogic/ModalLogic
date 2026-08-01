module

public import Neighborhood.Logic.Logic.ET
public import Neighborhood.Logic.Logic.ED

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicETD

/-- The axiom `D` is redundant over `T`. -/
theorem eq_LogicET : (@LogicETD α) = LogicET := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (⟨B, rfl⟩ | ⟨B, rfl⟩) <;> first | exact Logic.axiomT | exact Logic.axiomD
  · exact Hilbert.subset_of_subset_axioms (by grind)

instance : (@LogicETD α).IsConsistent := by
  rw [eq_LogicET]; infer_instance

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicETD α) := by
  rw [eq_LogicET]; exact LogicET.not_provable_axiomK a b hab

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicETD α) := by
  rw [eq_LogicET]; exact LogicET.not_provable_axiomM a b hab

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicETD α) := by
  rw [eq_LogicET]; exact LogicET.not_provable_axiomC a b hab

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicETD α) := by
  rw [eq_LogicET]; exact LogicET.not_provable_axiomN

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicETD α) := by
  rw [eq_LogicET]; exact LogicET.not_provable_axiomB a

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicETD α) := by
  rw [eq_LogicET]; exact LogicET.not_provable_axiomFour a

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicETD α) := by
  rw [eq_LogicET]; exact LogicET.not_provable_axiomFive a

end LogicETD

end
