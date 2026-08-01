module

public import Neighborhood.Logic.Logic.EKD
public import Neighborhood.Logic.Logic.EKP
public import Neighborhood.Logic.Logic.EDP

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEKDP

/-- The axiom `D` is redundant over `K` and `P`. -/
theorem eq_LogicEKP : (@LogicEKDP α) = LogicEKP := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, rfl⟩) | rfl) <;>
      first | exact Logic.axiomK | exact Logic.axiomP | exact Logic.axiomD
  · exact Hilbert.subset_of_subset_axioms (by grind)

instance : (@LogicEKDP α).IsConsistent := by
  rw [eq_LogicEKP]; infer_instance

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEKDP α) := by
  rw [eq_LogicEKP]; exact LogicEKP.not_provable_axiomM a b hab

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEKDP α) := by
  rw [eq_LogicEKP]; exact LogicEKP.not_provable_axiomC a b hab

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEKDP α) := by
  rw [eq_LogicEKP]; exact LogicEKP.not_provable_axiomN

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEKDP α) := by
  rw [eq_LogicEKP]; exact LogicEKP.not_provable_axiomT a

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEKDP α) := by
  rw [eq_LogicEKP]; exact LogicEKP.not_provable_axiomB a

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEKDP α) := by
  rw [eq_LogicEKP]; exact LogicEKP.not_provable_axiomFour a

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEKDP α) := by
  rw [eq_LogicEKP]; exact LogicEKP.not_provable_axiomFive a

end LogicEKDP

end
