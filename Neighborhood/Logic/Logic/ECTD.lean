module

public import Neighborhood.Logic.Logic.ECT
public import Neighborhood.Logic.Logic.ECD
public import Neighborhood.Logic.Logic.ETD

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECTD

/-- The axiom scheme `D` is redundant over `C` and `T`. -/
theorem eq_LogicECT : (@LogicECTD α) = LogicECT := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomC | exact Logic.axiomT | exact Logic.axiomD
  · exact Hilbert.subset_of_subset_axioms (by grind)

instance : (@LogicECTD α).IsConsistent := by
  rw [eq_LogicECT]; infer_instance

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicECTD α) := by
  rw [eq_LogicECT]; exact LogicECT.not_provable_axiomFour a

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECTD α) := by
  rw [eq_LogicECT]; exact LogicECT.not_provable_axiomM a b hab

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicECTD α) := by
  rw [eq_LogicECT]; exact LogicECT.not_provable_axiomN

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicECTD α) := by
  rw [eq_LogicECT]; exact LogicECT.not_provable_axiomK a b hab

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicECTD α) := by
  rw [eq_LogicECT]; exact LogicECT.not_provable_axiomB a

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicECTD α) := by
  rw [eq_LogicECT]; exact LogicECT.not_provable_axiomFive a

end LogicECTD

end
