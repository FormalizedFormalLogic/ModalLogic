module

public import Neighborhood.Logic.Logic.EMB
public import Neighborhood.Logic.Logic.EMC45
public import Neighborhood.Logic.Logic.ECB4
public import Neighborhood.Semantics.Example.Frame1_3

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMB4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsSymmetric]
    [F.IsTransitive] :
    A ∈ LogicEMB4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMB4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMB4.sound frame_1_2 hC⟩

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMB4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEMB4.sound frame_1_3 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEMB4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEMB4.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEMB4 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEMB4.sound frame_1_3 hcon)

theorem ssubset_LogicEMB : @LogicEMB ℕ ⊂ LogicEMB4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicEMB.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEMC45 : @LogicEMC45 ℕ ⊂ LogicEMB4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomFour |
        exact Logic.axiomFive
  · obtain ⟨A, hA⟩ := LogicEMC45.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicECB4 : @LogicECB4 ℕ ⊂ LogicEMB4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩)
    · exact Logic.axiomC
    · exact Logic.axiomB
    · exact Logic.axiomFour
  · obtain ⟨A, B, hA⟩ := LogicECB4.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

end LogicEMB4

end
