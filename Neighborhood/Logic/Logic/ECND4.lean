module

public import Neighborhood.Logic.Logic.ECND
public import Neighborhood.Logic.Logic.ECN4
public import Neighborhood.Logic.Logic.END4

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECND4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular]
    [F.ContainsUnit] [F.IsSerial] [F.IsTransitive] :
    A ∈ LogicECND4 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECND4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECND4.sound frame_1_2 hC⟩

end LogicECND4

theorem LogicECND4.ssubset_LogicECND : @LogicECND ℕ ⊂ LogicECND4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicECND.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicECND4.ssubset_LogicECN4 : @LogicECN4 ℕ ⊂ LogicECND4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicECN4.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicECND4.ssubset_LogicEND4 : @LogicEND4 ℕ ⊂ LogicECND4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicEND4.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

end
