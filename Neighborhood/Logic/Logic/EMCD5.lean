module

public import Neighborhood.Logic.Logic.EMC5
public import Neighborhood.Logic.Logic.EMCND
public import Neighborhood.Semantics.Example.Frame2_170

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMCD5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsRegular]
    [F.IsSerial] [F.IsEuclidean] :
    A ∈ LogicEMCD5 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMCD5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMCD5.sound frame_1_2 hC⟩

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMCD5 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicEMCD5.sound frame_2_170 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMCD5 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicEMCD5.sound frame_2_170 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMCD5 α) := by
  by_contra! hcon
  exact frame_3_10529440.not_valid_axiomFour (LogicEMCD5.sound frame_3_10529440 (hcon #a))

theorem ssubset_LogicEMC5 : @LogicEMC5 ℕ ⊂ LogicEMCD5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEMC5.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEMCND : @LogicEMCND ℕ ⊂ LogicEMCD5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEMCND.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

end LogicEMCD5

end
