module

public import Neighborhood.Logic.Logic.ETD
public import Neighborhood.Logic.Logic.ET4
public import Neighborhood.Logic.Logic.ED4

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicETD4

/-- The axiom `D` is redundant over `T`. -/
theorem eq_LogicET4 : (@LogicETD4 α) = LogicET4 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomT | exact Logic.axiomD | exact Logic.axiomFour
  · exact Hilbert.subset_of_subset_axioms (by grind)

instance : (@LogicETD4 α).IsConsistent := by
  rw [eq_LogicET4]; infer_instance

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicETD4 α) := by
  rw [eq_LogicET4]; exact LogicET4.not_provable_axiomK a b hab

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicETD4 α) := by
  rw [eq_LogicET4]; exact LogicET4.not_provable_axiomM a b hab

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicETD4 α) := by
  rw [eq_LogicET4]; exact LogicET4.not_provable_axiomC a b hab

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicETD4 α) := by
  rw [eq_LogicET4]; exact LogicET4.not_provable_axiomN

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicETD4 α) := by
  rw [eq_LogicET4]; exact LogicET4.not_provable_axiomB a

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicETD4 α) := by
  rw [eq_LogicET4]; exact LogicET4.not_provable_axiomFive a

end LogicETD4

end
