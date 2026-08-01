module

public import Neighborhood.Logic.Logic.ENT
public import Neighborhood.Logic.Logic.END
public import Neighborhood.Logic.Logic.ETD

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicENTD

/-- The axiom scheme `D` is redundant over `N` and `T`. -/
theorem eq_LogicENT : (@LogicENTD α) = LogicENT := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((rfl | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomT | exact Logic.axiomD
  · exact Hilbert.subset_of_subset_axioms (by grind)

instance : (@LogicENTD α).IsConsistent := by
  rw [eq_LogicENT]; infer_instance

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicENTD α) := by
  rw [eq_LogicENT]; exact LogicENT.not_provable_axiomB a

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicENTD α) := by
  rw [eq_LogicENT]; exact LogicENT.not_provable_axiomC a b hab

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicENTD α) := by
  rw [eq_LogicENT]; exact LogicENT.not_provable_axiomFour a

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicENTD α) := by
  rw [eq_LogicENT]; exact LogicENT.not_provable_axiomM a b hab

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicENTD α) := by
  rw [eq_LogicENT]; exact LogicENT.not_provable_axiomK a b hab

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicENTD α) := by
  rw [eq_LogicENT]; exact LogicENT.not_provable_axiomFive a

end LogicENTD

end
