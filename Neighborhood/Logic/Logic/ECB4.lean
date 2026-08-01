module

public import Neighborhood.Logic.Logic.ECN4
public import Neighborhood.Logic.Logic.ECNB
public import Neighborhood.Logic.Logic.EB4
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_191
public import Neighborhood.Semantics.Example.Frame3_9472136

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECB4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsSymmetric] [F.IsTransitive] :
    A ∈ LogicECB4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECB4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECB4.sound frame_1_2 hC⟩

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECB4 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomM hab (LogicECB4.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECB4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicECB4.sound frame_1_3 (hcon #a))

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicECB4 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomK hab (LogicECB4.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicECB4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicECB4.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicECB4 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicECB4.sound frame_1_3 hcon)

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicECB4 α) := by
  by_contra! hcon
  exact frame_2_191.not_valid_axiomFive (LogicECB4.sound frame_2_191 (hcon #a))

theorem ssubset_LogicECN4 : @LogicECN4 ℕ ⊂ LogicECB4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECN4.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicECNB : @LogicECNB ℕ ⊂ LogicECB4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECNB.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEB4 : @LogicEB4 ℕ ⊂ LogicECB4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicEB4.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

end LogicECB4

end
