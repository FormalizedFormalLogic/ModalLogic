module

public import Neighborhood.Logic.Logic.EMCD5
public import Neighborhood.Logic.Logic.EMCND4
public import Neighborhood.Logic.Logic.EMC45
public import Neighborhood.Logic.Logic.EMD45

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMCD45

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsRegular]
    [F.IsSerial] [F.IsTransitive] [F.IsEuclidean] :
    A ∈ LogicEMCD45 → F ⊧ A :=
  Hilbert.sound (by
    rintro _ ((((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMCD45 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMCD45.sound frame_1_2 hC⟩

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMCD45 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicEMCD45.sound frame_2_170 (hcon #a))

theorem ssubset_LogicEMCD5 : @LogicEMCD5 ℕ ⊂ LogicEMCD45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEMCD5.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEMCND4 : @LogicEMCND4 ℕ ⊂ LogicEMCD45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEMCND4.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEMC45 : @LogicEMC45 ℕ ⊂ LogicEMCD45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEMC45.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEMD45 : @LogicEMD45 ℕ ⊂ LogicEMCD45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicEMD45.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

end LogicEMCD45

end
