module

public import Neighborhood.Logic.Logic.ECP
public import Neighborhood.Logic.Logic.ECB
public import Neighborhood.Logic.Logic.EPB
public import Neighborhood.Semantics.Example.Frame2_140
public import Neighborhood.Semantics.Example.Frame3_9472136

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECPB

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.NotContainsEmpty]
    [F.IsSymmetric] :
    A ∈ LogicECPB → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECPB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECPB.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicECPB α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomK hab (LogicECPB.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECPB α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomM hab (LogicECPB.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECPB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomT (LogicECPB.sound frame_2_140 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicECPB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFour (LogicECPB.sound frame_2_140 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicECPB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFive (LogicECPB.sound frame_2_140 (hcon #a))

end LogicECPB

end
