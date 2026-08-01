module

public import Neighborhood.Logic.Logic.EKB
public import Neighborhood.Logic.Logic.EK4
public import Neighborhood.Logic.Logic.EB4
public import Neighborhood.Logic.Logic.EMB4

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEKB4

/-- `EKB4` and `EMB4` axiomatise the same logic: `M` is derivable from `K`, `B` and `4`, while
conversely `K` is derivable from `M`, `B` and `4`. -/
theorem eq_LogicEMB4 : (@LogicEKB4 α) = LogicEMB4 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomK | exact Logic.axiomB | exact Logic.axiomFour
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomB | exact Logic.axiomFour

instance : (@LogicEKB4 α).IsConsistent := by
  rw [eq_LogicEMB4]; infer_instance

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEKB4 α) := by
  rw [eq_LogicEMB4]; exact LogicEMB4.not_provable_axiomT a

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEKB4 α) := by
  rw [eq_LogicEMB4]; exact LogicEMB4.not_provable_axiomD a

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEKB4 α) := by
  rw [eq_LogicEMB4]; exact LogicEMB4.not_provable_axiomP

end LogicEKB4

end
