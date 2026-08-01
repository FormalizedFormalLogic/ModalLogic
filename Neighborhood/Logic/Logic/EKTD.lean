module

public import Neighborhood.Logic.Logic.EKT
public import Neighborhood.Logic.Logic.EKD
public import Neighborhood.Logic.Logic.ETD

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEKTD

/-- The axiom `D` is redundant over `K` and `T`. -/
theorem eq_LogicEKT : (@LogicEKTD α) = LogicEKT := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomK | exact Logic.axiomT | exact Logic.axiomD
  · exact Hilbert.subset_of_subset_axioms (by grind)

instance : (@LogicEKTD α).IsConsistent := by
  rw [eq_LogicEKT]; infer_instance

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEKTD α) := by
  rw [eq_LogicEKT]; exact LogicEKT.not_provable_axiomM a b hab

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEKTD α) := by
  rw [eq_LogicEKT]; exact LogicEKT.not_provable_axiomC a b hab

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEKTD α) := by
  rw [eq_LogicEKT]; exact LogicEKT.not_provable_axiomN

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEKTD α) := by
  rw [eq_LogicEKT]; exact LogicEKT.not_provable_axiomB a

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEKTD α) := by
  rw [eq_LogicEKT]; exact LogicEKT.not_provable_axiomFour a

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEKTD α) := by
  rw [eq_LogicEKT]; exact LogicEKT.not_provable_axiomFive a

end LogicEKTD

end
