module

public import Neighborhood.Logic.Logic.ECTB
public import Neighborhood.Logic.Logic.ECB4
public import Neighborhood.Logic.Logic.EC5
public import Neighborhood.Logic.Logic.ET5
public import Neighborhood.Semantics.Example.Frame3_9472136

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECT5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsReflexive]
    [F.IsEuclidean] :
    A ∈ LogicECT5 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECT5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECT5.sound frame_1_2 hC⟩

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECT5 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomM hab (LogicECT5.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicECT5 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomK hab (LogicECT5.sound frame_3_9472136 (hcon #a #b))

theorem ssubset_LogicECTB : @LogicECTB ℕ ⊂ LogicECT5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECTB.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicECB4 : @LogicECB4 ℕ ⊂ LogicECT5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECB4.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, Logic.axiomT, hA⟩

theorem ssubset_LogicET5 : @LogicET5 ℕ ⊂ LogicECT5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicET5.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEC5 : @LogicEC5 ℕ ⊂ LogicECT5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEC5.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, ProvableHilbert.axm (by grind), hA⟩

end LogicECT5

end
