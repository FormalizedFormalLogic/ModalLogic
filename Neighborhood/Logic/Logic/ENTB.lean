module

public import Neighborhood.Logic.Logic.ETB
public import Neighborhood.Logic.Logic.ENB
public import Neighborhood.Logic.Logic.ENT

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicENTB

/-- The axiom `N` is redundant over `T` and `B`. -/
theorem eq_LogicETB : (@LogicENTB α) = LogicETB := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((rfl | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomT | exact Logic.axiomB
  · exact Hilbert.subset_of_subset_axioms (by grind)

instance : (@LogicENTB α).IsConsistent := by
  rw [eq_LogicETB]; infer_instance

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicENTB α) := by
  rw [eq_LogicETB]; exact LogicETB.not_provable_axiomK a b hab

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicENTB α) := by
  rw [eq_LogicETB]; exact LogicETB.not_provable_axiomM a b hab

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicENTB α) := by
  rw [eq_LogicETB]; exact LogicETB.not_provable_axiomC a b hab

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicENTB α) := by
  rw [eq_LogicETB]; exact LogicETB.not_provable_axiomFour a

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicENTB α) := by
  rw [eq_LogicETB]; exact LogicETB.not_provable_axiomFive a

theorem ssubset_LogicENT : @LogicENT ℕ ⊂ LogicENTB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicENT.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, (ProvableHilbert.axm (by grind)), hA⟩

end LogicENTB

end
