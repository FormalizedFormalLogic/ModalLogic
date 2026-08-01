module

public import Neighborhood.Logic.Logic.ECN4
public import Neighborhood.Logic.Logic.ECN5
public import Neighborhood.Logic.Logic.EC45
public import Neighborhood.Logic.Logic.EN45

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECN45

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.ContainsUnit]
    [F.IsTransitive] [F.IsEuclidean] :
    A ∈ LogicECN45 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECN45 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECN45.sound frame_1_2 hC⟩

theorem ssubset_LogicECN4 : @LogicECN4 ℕ ⊂ LogicECN45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicECN4.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicECN5 : @LogicECN5 ℕ ⊂ LogicECN45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicECN5.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

end LogicECN45

end
