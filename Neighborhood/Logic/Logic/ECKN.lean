module

public import Neighborhood.Logic.Logic.ECK
public import Neighborhood.Logic.Logic.ECN
public import Neighborhood.Logic.Logic.EKN

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECKN

/-- The axiom `C` is redundant over `K` and `N`. -/
theorem eq_LogicEKN : (@LogicECKN α) = LogicEKN := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | rfl) <;>
      first | exact Logic.axiomC | exact Logic.axiomK | exact Logic.axiomN
  · exact Hilbert.subset_of_subset_axioms (by grind)

instance : (@LogicECKN α).IsConsistent := by
  rw [eq_LogicEKN]; infer_instance

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECKN α) := by
  rw [eq_LogicEKN]; exact LogicEKN.not_provable_axiomT a

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicECKN α) := by
  rw [eq_LogicEKN]; exact LogicEKN.not_provable_axiomB a

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicECKN α) := by
  rw [eq_LogicEKN]; exact LogicEKN.not_provable_axiomD a

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicECKN α) := by
  rw [eq_LogicEKN]; exact LogicEKN.not_provable_axiomP

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicECKN α) := by
  rw [eq_LogicEKN]; exact LogicEKN.not_provable_axiomFour a

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicECKN α) := by
  rw [eq_LogicEKN]; exact LogicEKN.not_provable_axiomFive a

end LogicECKN

end
