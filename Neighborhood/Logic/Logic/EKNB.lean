module

public import Neighborhood.Logic.Logic.EKN
public import Neighborhood.Logic.Logic.EKB
public import Neighborhood.Logic.Logic.ENB
public import Neighborhood.Logic.Logic.EMB

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEKNB

/-- `EKNB` and `EMB` axiomatise the same logic: `M` is derivable from `K` and `N`, while
conversely `K` is derivable from `M` and `B`. -/
theorem eq_LogicEMB : (@LogicEKNB α) = LogicEMB := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomK | exact Logic.axiomN | exact Logic.axiomB
  · apply Hilbert.subset_of_provable_axioms
    rintro A (⟨B, C, rfl⟩ | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomB

instance : (@LogicEKNB α).IsConsistent := by
  rw [eq_LogicEMB]; infer_instance

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEKNB α) := by
  rw [eq_LogicEMB]; exact LogicEMB.not_provable_axiomD a

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEKNB α) := by
  rw [eq_LogicEMB]; exact LogicEMB.not_provable_axiomFour a

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEKNB α) := by
  rw [eq_LogicEMB]; exact LogicEMB.not_provable_axiomT a

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEKNB α) := by
  rw [eq_LogicEMB]; exact LogicEMB.not_provable_axiomP

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEKNB α) := by
  rw [eq_LogicEMB]; exact LogicEMB.not_provable_axiomFive a

end LogicEKNB

end
