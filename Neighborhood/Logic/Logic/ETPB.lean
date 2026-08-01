module

public import Neighborhood.Logic.Logic.ETP
public import Neighborhood.Logic.Logic.ETB
public import Neighborhood.Logic.Logic.EPB

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicETPB

/-- The axiom `P` is redundant over `T`. -/
theorem eq_LogicETB : (@LogicETPB α) = LogicETB := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, rfl⟩ | rfl) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomP | exact Logic.axiomT | exact Logic.axiomB
  · exact Hilbert.subset_of_subset_axioms (by grind)

instance : (@LogicETPB α).IsConsistent := by
  rw [eq_LogicETB]; infer_instance

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicETPB α) := by
  rw [eq_LogicETB]; exact LogicETB.not_provable_axiomK a b hab

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicETPB α) := by
  rw [eq_LogicETB]; exact LogicETB.not_provable_axiomM a b hab

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicETPB α) := by
  rw [eq_LogicETB]; exact LogicETB.not_provable_axiomC a b hab

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicETPB α) := by
  rw [eq_LogicETB]; exact LogicETB.not_provable_axiomFour a

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicETPB α) := by
  rw [eq_LogicETB]; exact LogicETB.not_provable_axiomFive a

end LogicETPB

end
