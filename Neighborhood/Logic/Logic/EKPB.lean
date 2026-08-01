module

public import Neighborhood.Logic.Logic.EKP
public import Neighborhood.Logic.Logic.EKB
public import Neighborhood.Logic.Logic.EPB
public import Neighborhood.Logic.Logic.EMDB

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEKPB

/-- `EKPB` and `EMDB` axiomatise the same logic: `M` and `D` are derivable from `K`, `P` and `B`,
while conversely `K` and `P` are derivable from `M`, `D` and `B`. -/
theorem eq_LogicEMDB : (@LogicEKPB α) = LogicEMDB := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomK | exact Logic.axiomP | exact Logic.axiomB
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomD | exact Logic.axiomB

instance : (@LogicEKPB α).IsConsistent := by
  rw [eq_LogicEMDB]; infer_instance

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEKPB α) := by
  rw [eq_LogicEMDB]; exact LogicEMDB.not_provable_axiomT a

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEKPB α) := by
  rw [eq_LogicEMDB]; exact LogicEMDB.not_provable_axiomFour a

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEKPB α) := by
  rw [eq_LogicEMDB]; exact LogicEMDB.not_provable_axiomFive a

end LogicEKPB

end
