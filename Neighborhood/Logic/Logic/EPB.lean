module

public import Neighborhood.Logic.Logic.EP
public import Neighborhood.Logic.Logic.EB
public import Neighborhood.Semantics.Example.Frame2_140
public import Neighborhood.Semantics.Example.Frame3_8569504
public import Neighborhood.Semantics.Example.Frame3_9472136
public import Neighborhood.Semantics.Example.Frame3_9488552

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEPB

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.NotContainsEmpty] [F.IsSymmetric] :
    A ∈ LogicEPB → F ⊧ A :=
  Hilbert.sound (by rintro _ (rfl | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEPB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEPB.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEPB α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomK hab (LogicEPB.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEPB α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomM hab (LogicEPB.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEPB α) := by
  by_contra! hcon
  exact frame_3_9488552.not_valid_axiomC hab (LogicEPB.sound frame_3_9488552 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEPB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomT (LogicEPB.sound frame_2_140 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEPB α) := by
  by_contra! hcon
  exact frame_3_8569504.not_valid_axiomD (LogicEPB.sound frame_3_8569504 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEPB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFour (LogicEPB.sound frame_2_140 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEPB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFive (LogicEPB.sound frame_2_140 (hcon #a))

end LogicEPB

end
