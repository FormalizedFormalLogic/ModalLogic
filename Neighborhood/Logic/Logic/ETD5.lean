module

public import Neighborhood.Logic.Logic.ETD
public import Neighborhood.Logic.Logic.ET5
public import Neighborhood.Logic.Logic.ED5

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicETD5

/-- The axiom `D` is redundant over `T`. -/
theorem eq_LogicET5 : (@LogicETD5 α) = LogicET5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomT | exact Logic.axiomD | exact Logic.axiomFive
  · exact Hilbert.subset_of_subset_axioms (by grind)

instance : (@LogicETD5 α).IsConsistent := by
  rw [eq_LogicET5]; infer_instance

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicETD5 α) := by
  rw [eq_LogicET5]; exact LogicET5.not_provable_axiomK a b hab

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicETD5 α) := by
  rw [eq_LogicET5]; exact LogicET5.not_provable_axiomM a b hab

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicETD5 α) := by
  rw [eq_LogicET5]; exact LogicET5.not_provable_axiomC a b hab

end LogicETD5

end
