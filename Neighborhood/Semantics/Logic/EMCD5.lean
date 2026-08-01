module

public import Neighborhood.Semantics.Logic.EMC5
public import Neighborhood.Semantics.Logic.EMCND

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

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMCD5 α) := by
  by_contra! hcon
  exact frame_3_10529440.not_valid_axiomFour (LogicEMCD5.sound frame_3_10529440 (hcon #a))

end LogicEMCD5

theorem LogicEMC5_ssubset_LogicEMCD5 : @LogicEMC5 ℕ ⊂ LogicEMCD5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicEMC5.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEMCND_ssubset_LogicEMCD5 : @LogicEMCND ℕ ⊂ LogicEMCD5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomD
  · obtain ⟨A, hA⟩ := LogicEMCND.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

end
