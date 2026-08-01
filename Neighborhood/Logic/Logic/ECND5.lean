module

public import Neighborhood.Logic.Logic.ECND
public import Neighborhood.Logic.Logic.ECN5

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECND5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular]
    [F.ContainsUnit] [F.IsSerial] [F.IsEuclidean] :
    A ∈ LogicECND5 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECND5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECND5.sound frame_1_2 hC⟩

theorem ssubset_LogicECND : @LogicECND ℕ ⊂ LogicECND5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicECND.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicECN5 : @LogicECN5 ℕ ⊂ LogicECND5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicECN5.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

end LogicECND5

end
