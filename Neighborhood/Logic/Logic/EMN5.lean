module

public import Neighborhood.Logic.Logic.EN5
public import Neighborhood.Logic.Logic.EM5
public import Neighborhood.Logic.Logic.EMN

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMN5

/-- The axiom `N` is redundant over `M` and `5`. -/
theorem eq_LogicEM5 : (@LogicEMN5 α) = LogicEM5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomFive | exact Logic.axiomN
  · exact Hilbert.subset_of_subset_axioms (by grind)

instance : (@LogicEMN5 α).IsConsistent := by
  rw [eq_LogicEM5]; infer_instance

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEMN5 α) := by
  rw [eq_LogicEM5]; exact LogicEM5.not_provable_axiomK a b hab

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEMN5 α) := by
  rw [eq_LogicEM5]; exact LogicEM5.not_provable_axiomC a b hab

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMN5 α) := by
  rw [eq_LogicEM5]; exact LogicEM5.not_provable_axiomT a

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMN5 α) := by
  rw [eq_LogicEM5]; exact LogicEM5.not_provable_axiomB a

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEMN5 α) := by
  rw [eq_LogicEM5]; exact LogicEM5.not_provable_axiomD a

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEMN5 α) := by
  rw [eq_LogicEM5]; exact LogicEM5.not_provable_axiomP

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMN5 α) := by
  rw [eq_LogicEM5]; exact LogicEM5.not_provable_axiomFour a

end LogicEMN5

end
