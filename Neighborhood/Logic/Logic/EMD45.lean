module

public import Neighborhood.Logic.Logic.END45
public import Neighborhood.Logic.Logic.EMND4
public import Neighborhood.Logic.Logic.EMD5
public import Neighborhood.Logic.Logic.EM45
public import Neighborhood.Semantics.Example.Frame3_11053224

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMD45

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsSerial] [F.IsTransitive]
    [F.IsEuclidean] :
    A ∈ LogicEMD45 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMD45 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMD45.sound frame_1_2 hC⟩

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEMD45 α) := by
  by_contra! hcon
  exact frame_3_11053224.not_valid_axiomC hab (LogicEMD45.sound frame_3_11053224 (hcon #a #b))

theorem ssubset_LogicEND45 : @LogicEND45 ℕ ⊂ LogicEMD45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first
        | exact Logic.axiomN
        | exact Logic.axiomD
        | exact Logic.axiomFour
        | exact Logic.axiomFive
  · obtain ⟨A, B, hA⟩ := LogicEND45.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEMND4 : @LogicEMND4 ℕ ⊂ LogicEMD45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first
        | exact Logic.axiomM
        | exact Logic.axiomN
        | exact Logic.axiomD
        | exact Logic.axiomFour
  · obtain ⟨A, hA⟩ := LogicEMND4.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEMD5 : @LogicEMD5 ℕ ⊂ LogicEMD45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicEMD5.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEM45 : @LogicEM45 ℕ ⊂ LogicEMD45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicEM45.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

end LogicEMD45

end
