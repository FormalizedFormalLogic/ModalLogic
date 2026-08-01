module

public import Neighborhood.Logic.Logic.EDB
public import Neighborhood.Logic.Logic.ED5
public import Neighborhood.Logic.Logic.EB5
public import Neighborhood.Semantics.Example.Frame3_8815746
public import Neighborhood.Semantics.Example.Frame3_9472136
public import Neighborhood.Semantics.Example.Frame3_11570344

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEDB5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsSerial] [F.IsSymmetric] [F.IsEuclidean] :
    A ∈ LogicEDB5 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEDB5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEDB5.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEDB5 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomK hab (LogicEDB5.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEDB5 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomM hab (LogicEDB5.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEDB5 α) := by
  by_contra! hcon
  exact frame_3_11570344.not_valid_axiomC hab (LogicEDB5.sound frame_3_11570344 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEDB5 α) := by
  by_contra! hcon
  exact frame_3_8815746.not_valid_axiomT (LogicEDB5.sound frame_3_8815746 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEDB5 α) := by
  by_contra! hcon
  exact frame_3_8815746.not_valid_axiomFour (LogicEDB5.sound frame_3_8815746 (hcon #a))

end LogicEDB5

end
