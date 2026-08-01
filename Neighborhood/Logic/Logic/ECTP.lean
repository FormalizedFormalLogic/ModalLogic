module

public import Neighborhood.Logic.Logic.ECT
public import Neighborhood.Logic.Logic.ECP
public import Neighborhood.Logic.Logic.ETP

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECTP

/-- The axiom `P` is redundant over `C` and `T`. -/
theorem eq_LogicECT : (@LogicECTP α) = LogicECT := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, rfl⟩) | rfl) <;>
      first | exact Logic.axiomC | exact Logic.axiomP | exact Logic.axiomT
  · exact Hilbert.subset_of_subset_axioms (by grind)

instance : (@LogicECTP α).IsConsistent := by
  rw [eq_LogicECT]; infer_instance

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicECTP α) := by
  rw [eq_LogicECT]; exact LogicECT.not_provable_axiomFour a

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECTP α) := by
  rw [eq_LogicECT]; exact LogicECT.not_provable_axiomM a b hab

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicECTP α) := by
  rw [eq_LogicECT]; exact LogicECT.not_provable_axiomN

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicECTP α) := by
  rw [eq_LogicECT]; exact LogicECT.not_provable_axiomK a b hab

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicECTP α) := by
  rw [eq_LogicECT]; exact LogicECT.not_provable_axiomB a

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicECTP α) := by
  rw [eq_LogicECT]; exact LogicECT.not_provable_axiomFive a

end LogicECTP

end
