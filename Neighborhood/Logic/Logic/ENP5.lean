module

public import Neighborhood.Logic.Logic.ENP
public import Neighborhood.Logic.Logic.EN5
public import Neighborhood.Logic.Logic.EP5

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicENP5

/-- The axiom `N` is redundant over `P` and `5`. -/
theorem eq_LogicEP5 : (@LogicENP5 α) = LogicEP5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((rfl | rfl) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomP | exact Logic.axiomFive
  · exact Hilbert.subset_of_subset_axioms (by grind)

instance : (@LogicENP5 α).IsConsistent := by
  rw [eq_LogicEP5]; infer_instance

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicENP5 α) := by
  rw [eq_LogicEP5]; exact LogicEP5.not_provable_axiomK a b hab

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicENP5 α) := by
  rw [eq_LogicEP5]; exact LogicEP5.not_provable_axiomM a b hab

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicENP5 α) := by
  rw [eq_LogicEP5]; exact LogicEP5.not_provable_axiomC a b hab

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicENP5 α) := by
  rw [eq_LogicEP5]; exact LogicEP5.not_provable_axiomT a

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicENP5 α) := by
  rw [eq_LogicEP5]; exact LogicEP5.not_provable_axiomB a

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicENP5 α) := by
  rw [eq_LogicEP5]; exact LogicEP5.not_provable_axiomD a

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicENP5 α) := by
  rw [eq_LogicEP5]; exact LogicEP5.not_provable_axiomFour a

end LogicENP5

end
