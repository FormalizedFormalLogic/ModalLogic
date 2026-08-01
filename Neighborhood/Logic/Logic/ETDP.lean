module

public import Neighborhood.Logic.Logic.ETD
public import Neighborhood.Logic.Logic.ETP
public import Neighborhood.Logic.Logic.EDP
public import Neighborhood.Logic.Logic.ET

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicETDP

/-- The axioms `D` and `P` are redundant over `T`. -/
theorem eq_LogicET : (@LogicETDP α) = LogicET := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, rfl⟩ | ⟨B, rfl⟩) | rfl) <;>
      first | exact Logic.axiomP | exact Logic.axiomT | exact Logic.axiomD
  · exact Hilbert.subset_of_subset_axioms (by grind)

instance : (@LogicETDP α).IsConsistent := by
  rw [eq_LogicET]; infer_instance

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicETDP α) := by
  rw [eq_LogicET]; exact LogicET.not_provable_axiomK a b hab

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicETDP α) := by
  rw [eq_LogicET]; exact LogicET.not_provable_axiomM a b hab

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicETDP α) := by
  rw [eq_LogicET]; exact LogicET.not_provable_axiomC a b hab

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicETDP α) := by
  rw [eq_LogicET]; exact LogicET.not_provable_axiomN

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicETDP α) := by
  rw [eq_LogicET]; exact LogicET.not_provable_axiomB a

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicETDP α) := by
  rw [eq_LogicET]; exact LogicET.not_provable_axiomFour a

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicETDP α) := by
  rw [eq_LogicET]; exact LogicET.not_provable_axiomFive a

end LogicETDP

end
