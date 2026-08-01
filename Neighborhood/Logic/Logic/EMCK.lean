module

public import Neighborhood.Logic.Logic.EMK
public import Neighborhood.Logic.Logic.EMC

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMCK

/-- The axiom scheme `K` is redundant over `M` and `C`. -/
theorem eq_LogicEMC : (@LogicEMCK α) = LogicEMC := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | ⟨B, C, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomK_of_MC
  · exact Hilbert.subset_of_subset_axioms (by grind)

instance : (@LogicEMCK α).IsConsistent := by
  rw [eq_LogicEMC]; infer_instance

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEMCK α) := by
  rw [eq_LogicEMC]; exact LogicEMC.not_provable_axiomN

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMCK α) := by
  rw [eq_LogicEMC]; exact LogicEMC.not_provable_axiomT a

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMCK α) := by
  rw [eq_LogicEMC]; exact LogicEMC.not_provable_axiomB a

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEMCK α) := by
  rw [eq_LogicEMC]; exact LogicEMC.not_provable_axiomD a

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEMCK α) := by
  rw [eq_LogicEMC]; exact LogicEMC.not_provable_axiomP

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMCK α) := by
  rw [eq_LogicEMC]; exact LogicEMC.not_provable_axiomFour a

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMCK α) := by
  rw [eq_LogicEMC]; exact LogicEMC.not_provable_axiomFive a

/-- The axiom scheme `C` is redundant over `M` and `K`. -/
theorem eq_LogicEMK : (@LogicEMCK α) = LogicEMK := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | ⟨B, C, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomK
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicEMCK

end
