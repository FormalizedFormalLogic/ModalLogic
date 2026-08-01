module

public import Neighborhood.Logic.Logic.EDB5
public import Neighborhood.Logic.Logic.ECB5
public import Neighborhood.Logic.Logic.ECD5
public import Neighborhood.Logic.Logic.ECDB
public import Neighborhood.Logic.Logic.ECT5
public import Neighborhood.Semantics.Example.Frame3_9472136

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECDB5

/-- Over `EC`, the axioms `D`, `B` and `5` derive `T`, and conversely `T` and `5` derive
`D` and `B`. -/
theorem eq_LogicECT5 : (@LogicECDB5 α) = LogicECT5 := by
  hilbert_eq_axioms

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsSerial] [F.IsSymmetric]
    [F.IsEuclidean] :
    A ∈ LogicECDB5 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECDB5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECDB5.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicECDB5 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomK hab (LogicECDB5.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECDB5 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomM hab (LogicECDB5.sound frame_3_9472136 (hcon #a #b))

theorem ssubset_LogicECB5 : @LogicECB5 ℕ ⊂ LogicECDB5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECB5.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, ProvableHilbert.axm (by grind), hA⟩

theorem ssubset_LogicECD5 : @LogicECD5 ℕ ⊂ LogicECDB5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECD5.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, ProvableHilbert.axm (by grind), hA⟩

theorem ssubset_LogicECDB : @LogicECDB ℕ ⊂ LogicECDB5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECDB.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, ProvableHilbert.axm (by grind), hA⟩

theorem ssubset_LogicEDB5 : @LogicEDB5 ℕ ⊂ LogicECDB5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicEDB5.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, ProvableHilbert.axm (by grind), hA⟩

end LogicECDB5

end
