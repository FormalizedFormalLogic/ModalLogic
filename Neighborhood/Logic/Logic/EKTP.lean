module

public import Neighborhood.Logic.Logic.EKT
public import Neighborhood.Logic.Logic.EKP
public import Neighborhood.Logic.Logic.ETP

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEKTP

/-- The axiom `P` is redundant over `K` and `T`. -/
theorem eq_LogicEKT : (@LogicEKTP α) = LogicEKT := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, rfl⟩) | rfl) <;>
      first | exact Logic.axiomK | exact Logic.axiomP | exact Logic.axiomT
  · exact Hilbert.subset_of_subset_axioms (by grind)

instance : (@LogicEKTP α).IsConsistent := by
  rw [eq_LogicEKT]; infer_instance

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEKTP α) := by
  rw [eq_LogicEKT]; exact LogicEKT.not_provable_axiomM a b hab

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEKTP α) := by
  rw [eq_LogicEKT]; exact LogicEKT.not_provable_axiomC a b hab

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEKTP α) := by
  rw [eq_LogicEKT]; exact LogicEKT.not_provable_axiomN

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEKTP α) := by
  rw [eq_LogicEKT]; exact LogicEKT.not_provable_axiomB a

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEKTP α) := by
  rw [eq_LogicEKT]; exact LogicEKT.not_provable_axiomFour a

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEKTP α) := by
  rw [eq_LogicEKT]; exact LogicEKT.not_provable_axiomFive a

end LogicEKTP

end
