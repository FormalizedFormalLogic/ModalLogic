module

public import Neighborhood.Logic.Logic.EKT
public import Neighborhood.Logic.Logic.EKB
public import Neighborhood.Logic.Logic.ETB
public import Neighborhood.Logic.Logic.EMTB

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEKTB

/-- `EKTB` and `EMTB` axiomatise the same logic: `M` is derivable from `K`, `T` and `B`, while
conversely `K` is derivable from `M`, `T` and `B`. -/
theorem eq_LogicEMTB : (@LogicEKTB α) = LogicEMTB := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomK | exact Logic.axiomT | exact Logic.axiomB
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomT | exact Logic.axiomB

instance : (@LogicEKTB α).IsConsistent := by
  rw [eq_LogicEMTB]; infer_instance

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEKTB α) := by
  rw [eq_LogicEMTB]; exact LogicEMTB.not_provable_axiomFive a

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEKTB α) := by
  rw [eq_LogicEMTB]; exact LogicEMTB.not_provable_axiomFour a

end LogicEKTB

end
