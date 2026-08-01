module

public import Neighborhood.Logic.Logic.ETP
public import Neighborhood.Logic.Logic.ET4
public import Neighborhood.Logic.Logic.EP4

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicETP4

/-- The axiom `P` is redundant over `T`. -/
theorem eq_LogicET4 : (@LogicETP4 α) = LogicET4 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, rfl⟩ | rfl) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomP | exact Logic.axiomT | exact Logic.axiomFour
  · exact Hilbert.subset_of_subset_axioms (by grind)

instance : (@LogicETP4 α).IsConsistent := by
  rw [eq_LogicET4]; infer_instance

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicETP4 α) := by
  rw [eq_LogicET4]; exact LogicET4.not_provable_axiomK a b hab

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicETP4 α) := by
  rw [eq_LogicET4]; exact LogicET4.not_provable_axiomM a b hab

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicETP4 α) := by
  rw [eq_LogicET4]; exact LogicET4.not_provable_axiomC a b hab

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicETP4 α) := by
  rw [eq_LogicET4]; exact LogicET4.not_provable_axiomN

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicETP4 α) := by
  rw [eq_LogicET4]; exact LogicET4.not_provable_axiomB a

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicETP4 α) := by
  rw [eq_LogicET4]; exact LogicET4.not_provable_axiomFive a

end LogicETP4

end
