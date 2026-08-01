module

public import Neighborhood.Logic.Logic.EMCN4
import Neighborhood.Logic.Logic.EMCND

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMCND4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsRegular] [F.ContainsUnit] [F.IsTransitive] [F.IsSerial] :
    A ∈ LogicEMCND4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMCND4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMCND4.sound frame_1_2 hC⟩

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMCND4 α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomFive (LogicEMCND4.sound frame_2_138 (hcon #a))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMCND4 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicEMCND4.sound frame_2_170 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMCND4 α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicEMCND4.sound frame_2_138 (hcon #a))

theorem ssubset_LogicEMCN4 : @LogicEMCN4 ℕ ⊂ LogicEMCND4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEMCN4.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEMCND : @LogicEMCND ℕ ⊂ LogicEMCND4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEMCND.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

end LogicEMCND4

end
