module

public import Neighborhood.Logic.Logic.ETP
public import Neighborhood.Logic.Logic.ET5
public import Neighborhood.Logic.Logic.EP5

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicETP5

/-- The axiom `P` is redundant over `T`. -/
theorem eq_LogicET5 : (@LogicETP5 α) = LogicET5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, rfl⟩ | rfl) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomP | exact Logic.axiomT | exact Logic.axiomFive
  · exact Hilbert.subset_of_subset_axioms (by grind)

instance : (@LogicETP5 α).IsConsistent := by
  rw [eq_LogicET5]; infer_instance

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicETP5 α) := by
  rw [eq_LogicET5]; exact LogicET5.not_provable_axiomK a b hab

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicETP5 α) := by
  rw [eq_LogicET5]; exact LogicET5.not_provable_axiomM a b hab

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicETP5 α) := by
  rw [eq_LogicET5]; exact LogicET5.not_provable_axiomC a b hab

end LogicETP5

end
