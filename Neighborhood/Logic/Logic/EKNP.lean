module

public import Neighborhood.Logic.Logic.EKN
public import Neighborhood.Logic.Logic.EKP
public import Neighborhood.Logic.Logic.ENP
public import Neighborhood.Logic.Logic.EKND

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEKNP

/-- `EKNP` and `EKND` axiomatise the same logic: `D` is derivable from `K` and `P`, while
conversely `P` is derivable from `N` and `D`. -/
theorem eq_LogicEKND : (@LogicEKNP α) = LogicEKND := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | rfl) | rfl) <;>
      first | exact Logic.axiomK | exact Logic.axiomN | exact Logic.axiomP
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomK | exact Logic.axiomN | exact Logic.axiomD

instance : (@LogicEKNP α).IsConsistent := by
  rw [eq_LogicEKND]; infer_instance

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEKNP α) := by
  rw [eq_LogicEKND]; exact LogicEKND.not_provable_axiomT a

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEKNP α) := by
  rw [eq_LogicEKND]; exact LogicEKND.not_provable_axiomB a

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEKNP α) := by
  rw [eq_LogicEKND]; exact LogicEKND.not_provable_axiomFour a

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEKNP α) := by
  rw [eq_LogicEKND]; exact LogicEKND.not_provable_axiomFive a

end LogicEKNP

end
