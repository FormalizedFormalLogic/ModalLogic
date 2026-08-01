module

public import Neighborhood.Logic.Logic.ECD
public import Neighborhood.Logic.Logic.ECP
public import Neighborhood.Logic.Logic.EDP

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECDP

/-- The axiom scheme `D` is redundant over `C` and `P`. -/
theorem eq_LogicECP : (@LogicECDP α) = LogicECP := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, rfl⟩) | rfl) <;>
      first | exact Logic.axiomC | exact Logic.axiomD | exact Logic.axiomP
  · exact Hilbert.subset_of_subset_axioms (by grind)

instance : (@LogicECDP α).IsConsistent := by
  rw [eq_LogicECP]; infer_instance

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECDP α) := by
  rw [eq_LogicECP]; exact LogicECP.not_provable_axiomM a b hab

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicECDP α) := by
  rw [eq_LogicECP]; exact LogicECP.not_provable_axiomN

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicECDP α) := by
  rw [eq_LogicECP]; exact LogicECP.not_provable_axiomK a b hab

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECDP α) := by
  rw [eq_LogicECP]; exact LogicECP.not_provable_axiomT a

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicECDP α) := by
  rw [eq_LogicECP]; exact LogicECP.not_provable_axiomB a

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicECDP α) := by
  rw [eq_LogicECP]; exact LogicECP.not_provable_axiomFour a

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicECDP α) := by
  rw [eq_LogicECP]; exact LogicECP.not_provable_axiomFive a

end LogicECDP

end
