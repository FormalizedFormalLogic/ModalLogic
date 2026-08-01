module

public import Neighborhood.Logic.Logic.EDP
public import Neighborhood.Logic.Logic.EDB
public import Neighborhood.Logic.Logic.EPB
public import Neighborhood.Logic.Logic.ENDB

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEDPB

/-- `EDPB` and `ENDB` axiomatise the same logic: `P` is derivable from `D` and `N`, while
conversely `N` is derivable from `P` and `B`. -/
theorem eq_LogicENDB : (@LogicEDPB α) = LogicENDB := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, rfl⟩ | rfl) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomD | exact Logic.axiomP | exact Logic.axiomB
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((rfl | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomD | exact Logic.axiomB

instance : (@LogicEDPB α).IsConsistent := by
  rw [eq_LogicENDB]; infer_instance

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEDPB α) := by
  rw [eq_LogicENDB]; exact LogicENDB.not_provable_axiomK a b hab

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEDPB α) := by
  rw [eq_LogicENDB]; exact LogicENDB.not_provable_axiomM a b hab

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEDPB α) := by
  rw [eq_LogicENDB]; exact LogicENDB.not_provable_axiomC a b hab

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEDPB α) := by
  rw [eq_LogicENDB]; exact LogicENDB.not_provable_axiomT a

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEDPB α) := by
  rw [eq_LogicENDB]; exact LogicENDB.not_provable_axiomFour a

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEDPB α) := by
  rw [eq_LogicENDB]; exact LogicENDB.not_provable_axiomFive a

end LogicEDPB

end
