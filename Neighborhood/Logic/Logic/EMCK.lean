module

public import Neighborhood.Logic.Logic.EMK
public import Neighborhood.Logic.Logic.EMC
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_8

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMCK

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsRegular]
    [F.HasPropertyK] :
    A ∈ LogicEMCK → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) <;> simp)

instance : (@LogicEMCK α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMCK.sound frame_1_2 hC⟩

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEMCK α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEMCK.sound frame_1_0 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMCK α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEMCK.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMCK α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEMCK.sound frame_1_0 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEMCK α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEMCK.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEMCK α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEMCK.sound frame_1_3 hcon)

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMCK α) := by
  by_contra! hcon
  exact frame_2_8.not_valid_axiomFour (LogicEMCK.sound frame_2_8 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMCK α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEMCK.sound frame_1_0 (hcon #a))

/-- The axiom scheme `K` is redundant over `M` and `C`. -/
theorem eq_LogicEMC : (@LogicEMCK α) = LogicEMC := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | ⟨B, C, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomK_of_MC
  · exact Hilbert.subset_of_subset_axioms (by grind)

/-- The axiom scheme `C` is redundant over `M` and `K`. -/
theorem eq_LogicEMK : (@LogicEMCK α) = LogicEMK := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | ⟨B, C, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomK
  · exact Hilbert.subset_of_subset_axioms (by grind)

end LogicEMCK

end
