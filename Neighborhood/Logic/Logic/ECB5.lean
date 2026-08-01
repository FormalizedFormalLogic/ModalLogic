module

public import Neighborhood.Logic.Logic.ECB
public import Neighborhood.Logic.Logic.EC5
public import Neighborhood.Logic.Logic.EB5
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_79
public import Neighborhood.Semantics.Example.Frame2_95
public import Neighborhood.Semantics.Example.Frame3_9472136

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECB5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsSymmetric]
    [F.IsEuclidean] :
    A ∈ LogicECB5 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECB5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECB5.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicECB5 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomK hab (LogicECB5.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECB5 α) := by
  by_contra! hcon
  exact frame_2_79.not_valid_axiomM hab (LogicECB5.sound frame_2_79 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicECB5 α) := by
  intro hcon
  exact frame_2_95.not_valid_axiomN (LogicECB5.sound frame_2_95 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECB5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicECB5.sound frame_1_3 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicECB5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicECB5.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicECB5 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicECB5.sound frame_1_3 hcon)

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicECB5 α) := by
  by_contra! hcon
  exact frame_2_79.not_valid_axiomFour (LogicECB5.sound frame_2_79 (hcon #a))

theorem ssubset_LogicEB5 : @LogicEB5 ℕ ⊂ LogicECB5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicEB5.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, ProvableHilbert.axm (by grind), hA⟩

theorem ssubset_LogicEC5 : @LogicEC5 ℕ ⊂ LogicECB5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEC5.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, ProvableHilbert.axm (by grind), hA⟩

theorem ssubset_LogicECB : @LogicECB ℕ ⊂ LogicECB5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECB.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, ProvableHilbert.axm (by grind), hA⟩

end LogicECB5

end
