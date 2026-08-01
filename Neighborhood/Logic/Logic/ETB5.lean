module

public import Neighborhood.Logic.Logic.ETB
public import Neighborhood.Logic.Logic.ET5
public import Neighborhood.Logic.Logic.EB5

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicETB5

/-- The axiom `B` is redundant over `T` and `5`. -/
theorem eq_LogicET5 : (@LogicETB5 α) = LogicET5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomT | exact Logic.axiomB | exact Logic.axiomFive
  · exact Hilbert.subset_of_subset_axioms (by grind)

instance : (@LogicETB5 α).IsConsistent := by
  rw [eq_LogicET5]; infer_instance

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicETB5 α) := by
  rw [eq_LogicET5]; exact LogicET5.not_provable_axiomK a b hab

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicETB5 α) := by
  rw [eq_LogicET5]; exact LogicET5.not_provable_axiomM a b hab

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicETB5 α) := by
  rw [eq_LogicET5]; exact LogicET5.not_provable_axiomC a b hab

end LogicETB5

end
