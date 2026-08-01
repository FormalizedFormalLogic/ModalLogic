module

public import Neighborhood.Logic.Logic.EMC4

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMCD4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsRegular] [F.IsTransitive] [F.IsSerial] :
    A ∈ LogicEMCD4 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMCD4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMCD4.sound frame_1_2 hC⟩

theorem ssubset_LogicEMC4 : @LogicEMC4 ℕ ⊂ LogicEMCD4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicEMC4.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

end LogicEMCD4

end
