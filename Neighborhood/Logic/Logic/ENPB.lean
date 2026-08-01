module

public import Neighborhood.Logic.Logic.ENP
public import Neighborhood.Logic.Logic.ENB
public import Neighborhood.Logic.Logic.EPB

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicENPB

/-- The axiom `N` is redundant over `P` and `B`. -/
theorem eq_LogicEPB : (@LogicENPB α) = LogicEPB := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((rfl | rfl) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomP | exact Logic.axiomB
  · exact Hilbert.subset_of_subset_axioms (by grind)

instance : (@LogicENPB α).IsConsistent := by
  rw [eq_LogicEPB]; infer_instance

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicENPB α) := by
  rw [eq_LogicEPB]; exact LogicEPB.not_provable_axiomK a b hab

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicENPB α) := by
  rw [eq_LogicEPB]; exact LogicEPB.not_provable_axiomM a b hab

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicENPB α) := by
  rw [eq_LogicEPB]; exact LogicEPB.not_provable_axiomC a b hab

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicENPB α) := by
  rw [eq_LogicEPB]; exact LogicEPB.not_provable_axiomT a

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicENPB α) := by
  rw [eq_LogicEPB]; exact LogicEPB.not_provable_axiomD a

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicENPB α) := by
  rw [eq_LogicEPB]; exact LogicEPB.not_provable_axiomFour a

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicENPB α) := by
  rw [eq_LogicEPB]; exact LogicEPB.not_provable_axiomFive a

end LogicENPB

end
