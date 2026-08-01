module

public import Neighborhood.Logic.Logic.ET
public import Neighborhood.Logic.Logic.EP

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicETP

/-- The axiom `P` is redundant over `T`. -/
theorem eq_LogicET : (@LogicETP α) = LogicET := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (⟨B, rfl⟩ | rfl) <;> first | exact Logic.axiomP | exact Logic.axiomT
  · exact Hilbert.subset_of_subset_axioms (by grind)

instance : (@LogicETP α).IsConsistent := by
  rw [eq_LogicET]; infer_instance

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicETP α) := by
  rw [eq_LogicET]; exact LogicET.not_provable_axiomK a b hab

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicETP α) := by
  rw [eq_LogicET]; exact LogicET.not_provable_axiomM a b hab

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicETP α) := by
  rw [eq_LogicET]; exact LogicET.not_provable_axiomC a b hab

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicETP α) := by
  rw [eq_LogicET]; exact LogicET.not_provable_axiomN

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicETP α) := by
  rw [eq_LogicET]; exact LogicET.not_provable_axiomB a

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicETP α) := by
  rw [eq_LogicET]; exact LogicET.not_provable_axiomFour a

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicETP α) := by
  rw [eq_LogicET]; exact LogicET.not_provable_axiomFive a

end LogicETP

end
