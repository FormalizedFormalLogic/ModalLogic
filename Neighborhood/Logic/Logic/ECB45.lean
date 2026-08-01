module

public import Neighborhood.Logic.Logic.EB45
public import Neighborhood.Logic.Logic.EC45
public import Neighborhood.Logic.Logic.ECB5
public import Neighborhood.Logic.Logic.ECB4
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame3_9472136

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECB45

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsSymmetric] [F.IsTransitive]
    [F.IsEuclidean] :
    A ∈ LogicECB45 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECB45 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECB45.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicECB45 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomK hab (LogicECB45.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECB45 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomM hab (LogicECB45.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECB45 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicECB45.sound frame_1_3 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicECB45 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicECB45.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicECB45 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicECB45.sound frame_1_3 hcon)

theorem ssubset_LogicEB45 : @LogicEB45 ℕ ⊂ LogicECB45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicEB45.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, ProvableHilbert.axm (by grind), hA⟩

theorem ssubset_LogicEC45 : @LogicEC45 ℕ ⊂ LogicECB45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEC45.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, ProvableHilbert.axm (by grind), hA⟩

theorem ssubset_LogicECB4 : @LogicECB4 ℕ ⊂ LogicECB45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECB4.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, ProvableHilbert.axm (by grind), hA⟩

theorem ssubset_LogicECB5 : @LogicECB5 ℕ ⊂ LogicECB45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECB5.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, ProvableHilbert.axm (by grind), hA⟩

end LogicECB45

end
