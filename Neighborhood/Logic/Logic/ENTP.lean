module

public import Neighborhood.Logic.Logic.ENT
public import Neighborhood.Logic.Logic.ENP
public import Neighborhood.Logic.Logic.ETP

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicENTP

/-- The axiom `P` is redundant over `N` and `T`. -/
theorem eq_LogicENT : (@LogicENTP α) = LogicENT := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((rfl | ⟨B, rfl⟩) | rfl) <;>
      first | exact Logic.axiomN | exact Logic.axiomP | exact Logic.axiomT
  · exact Hilbert.subset_of_subset_axioms (by grind)

instance : (@LogicENTP α).IsConsistent := by
  rw [eq_LogicENT]; infer_instance

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicENTP α) := by
  rw [eq_LogicENT]; exact LogicENT.not_provable_axiomB a

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicENTP α) := by
  rw [eq_LogicENT]; exact LogicENT.not_provable_axiomC a b hab

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicENTP α) := by
  rw [eq_LogicENT]; exact LogicENT.not_provable_axiomFour a

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicENTP α) := by
  rw [eq_LogicENT]; exact LogicENT.not_provable_axiomM a b hab

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicENTP α) := by
  rw [eq_LogicENT]; exact LogicENT.not_provable_axiomK a b hab

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicENTP α) := by
  rw [eq_LogicENT]; exact LogicENT.not_provable_axiomFive a

end LogicENTP

end
