module

public import Neighborhood.Logic.Logic.ETD
public import Neighborhood.Logic.Logic.ETB
public import Neighborhood.Logic.Logic.EDB

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicETDB

/-- The axiom `D` is redundant over `T` and `B`. -/
theorem eq_LogicETB : (@LogicETDB α) = LogicETB := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomT | exact Logic.axiomD | exact Logic.axiomB
  · exact Hilbert.subset_of_subset_axioms (by grind)

instance : (@LogicETDB α).IsConsistent := by
  rw [eq_LogicETB]; infer_instance

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicETDB α) := by
  rw [eq_LogicETB]; exact LogicETB.not_provable_axiomK a b hab

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicETDB α) := by
  rw [eq_LogicETB]; exact LogicETB.not_provable_axiomM a b hab

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicETDB α) := by
  rw [eq_LogicETB]; exact LogicETB.not_provable_axiomC a b hab

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicETDB α) := by
  rw [eq_LogicETB]; exact LogicETB.not_provable_axiomFour a

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicETDB α) := by
  rw [eq_LogicETB]; exact LogicETB.not_provable_axiomFive a

end LogicETDB

end
