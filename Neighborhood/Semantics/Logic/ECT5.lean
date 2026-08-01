module

public import Neighborhood.Semantics.Logic.ECTB
public import Neighborhood.Semantics.Logic.ECB4
public import Neighborhood.Semantics.Logic.ET5
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

end LogicECT5

theorem LogicECTB_ssubset_LogicECT5 : @LogicECTB ℕ ⊂ LogicECT5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomC | exact Logic.axiomT | exact Logic.axiomB
  · obtain ⟨A, hA⟩ := LogicECTB.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicECB4_ssubset_LogicECT5 : @LogicECB4 ℕ ⊂ LogicECT5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩)
    · exact Logic.axiomC
    · exact Logic.axiomB
    · exact Logic.axiomFour
  · obtain ⟨A, hA⟩ := LogicECB4.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, Logic.axiomT, hA⟩

theorem LogicET5_ssubset_LogicECT5 : @LogicET5 ℕ ⊂ LogicECT5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicET5.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

end
