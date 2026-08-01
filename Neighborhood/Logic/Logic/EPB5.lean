module

public import Neighborhood.Logic.Logic.EPB
public import Neighborhood.Logic.Logic.EP5
public import Neighborhood.Logic.Logic.EB5
public import Neighborhood.Semantics.Example.Frame3_8815746
public import Neighborhood.Semantics.Example.Frame3_9472136
public import Neighborhood.Semantics.Example.Frame3_9473180
public import Neighborhood.Semantics.Example.Frame3_11570344

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEPB5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.NotContainsEmpty] [F.IsSymmetric]
    [F.IsEuclidean] :
    A ∈ LogicEPB5 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEPB5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEPB5.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEPB5 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomK hab (LogicEPB5.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEPB5 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomM hab (LogicEPB5.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEPB5 α) := by
  by_contra! hcon
  exact frame_3_11570344.not_valid_axiomC hab (LogicEPB5.sound frame_3_11570344 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEPB5 α) := by
  by_contra! hcon
  exact frame_3_8815746.not_valid_axiomT (LogicEPB5.sound frame_3_8815746 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEPB5 α) := by
  by_contra! hcon
  exact frame_3_9473180.not_valid_axiomD (LogicEPB5.sound frame_3_9473180 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEPB5 α) := by
  by_contra! hcon
  exact frame_3_8815746.not_valid_axiomFour (LogicEPB5.sound frame_3_8815746 (hcon #a))

end LogicEPB5

end
