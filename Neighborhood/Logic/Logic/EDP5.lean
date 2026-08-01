module

public import Neighborhood.Logic.Logic.EDP
public import Neighborhood.Logic.Logic.ED5
public import Neighborhood.Logic.Logic.EP5
public import Neighborhood.Logic.Logic.END5

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEDP5

/-- `EDP5` and `END5` axiomatise the same logic: `P` is derivable from `D` and `N`, while
conversely `N` is derivable from `P` and `5`. -/
theorem eq_LogicEND5 : (@LogicEDP5 α) = LogicEND5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, rfl⟩ | rfl) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomD | exact Logic.axiomP | exact Logic.axiomFive
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((rfl | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomD | exact Logic.axiomFive

instance : (@LogicEDP5 α).IsConsistent := by
  rw [eq_LogicEND5]; infer_instance

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEDP5 α) := by
  rw [eq_LogicEND5]; exact LogicEND5.not_provable_axiomK a b hab

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEDP5 α) := by
  rw [eq_LogicEND5]; exact LogicEND5.not_provable_axiomM a b hab

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEDP5 α) := by
  rw [eq_LogicEND5]; exact LogicEND5.not_provable_axiomC a b hab

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEDP5 α) := by
  rw [eq_LogicEND5]; exact LogicEND5.not_provable_axiomT a

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEDP5 α) := by
  rw [eq_LogicEND5]; exact LogicEND5.not_provable_axiomB a

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEDP5 α) := by
  rw [eq_LogicEND5]; exact LogicEND5.not_provable_axiomFour a

end LogicEDP5

end
