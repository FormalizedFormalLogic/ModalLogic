module

public import Neighborhood.Logic.Logic.EKN
public import Neighborhood.Logic.Logic.EK5
public import Neighborhood.Logic.Logic.EN5
public import Neighborhood.Logic.Logic.EMC5

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEKN5

/-- `EKN5` and `EMC5` axiomatise the same logic: `M` and `C` are derivable from `K`, `N` and
`5`, while conversely `K` and `N` are derivable from `M`, `C` and `5`. -/
theorem eq_LogicEMC5 : (@LogicEKN5 α) = LogicEMC5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomK | exact Logic.axiomN | exact Logic.axiomFive
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomFive

instance : (@LogicEKN5 α).IsConsistent := by
  rw [eq_LogicEMC5]; infer_instance

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEKN5 α) := by
  rw [eq_LogicEMC5]; exact LogicEMC5.not_provable_axiomD a

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEKN5 α) := by
  rw [eq_LogicEMC5]; exact LogicEMC5.not_provable_axiomFour a

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEKN5 α) := by
  rw [eq_LogicEMC5]; exact LogicEMC5.not_provable_axiomT a

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEKN5 α) := by
  rw [eq_LogicEMC5]; exact LogicEMC5.not_provable_axiomB a

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEKN5 α) := by
  rw [eq_LogicEMC5]; exact LogicEMC5.not_provable_axiomP

end LogicEKN5

end
