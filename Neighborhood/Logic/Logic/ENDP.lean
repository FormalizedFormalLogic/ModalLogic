module

public import Neighborhood.Logic.Logic.END
public import Neighborhood.Logic.Logic.ENP
public import Neighborhood.Logic.Logic.EDP

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicENDP

/-- The axiom `P` is redundant over `N` and `D`. -/
theorem eq_LogicEND : (@LogicENDP α) = LogicEND := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((rfl | ⟨B, rfl⟩) | rfl) <;>
      first | exact Logic.axiomN | exact Logic.axiomD | exact Logic.axiomP
  · exact Hilbert.subset_of_subset_axioms (by grind)

instance : (@LogicENDP α).IsConsistent := by
  rw [eq_LogicEND]; infer_instance

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicENDP α) := by
  rw [eq_LogicEND]; exact LogicEND.not_provable_axiomB a

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicENDP α) := by
  rw [eq_LogicEND]; exact LogicEND.not_provable_axiomC a b hab

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicENDP α) := by
  rw [eq_LogicEND]; exact LogicEND.not_provable_axiomFive a

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicENDP α) := by
  rw [eq_LogicEND]; exact LogicEND.not_provable_axiomFour a

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicENDP α) := by
  rw [eq_LogicEND]; exact LogicEND.not_provable_axiomM a b hab

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicENDP α) := by
  rw [eq_LogicEND]; exact LogicEND.not_provable_axiomT a

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicENDP α) := by
  rw [eq_LogicEND]; exact LogicEND.not_provable_axiomK a b hab

end LogicENDP

end
