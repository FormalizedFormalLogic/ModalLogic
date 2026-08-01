module

public import Neighborhood.Logic.Logic.ECK
public import Neighborhood.Logic.Logic.ECD
public import Neighborhood.Logic.Logic.EKD
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame1_1
public import Neighborhood.Semantics.Example.Frame2_140

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECKD

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.HasPropertyK] [F.IsSerial] :
    A ∈ LogicECKD → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECKD α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECKD.sound frame_1_2 hC⟩

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECKD α) := by
  by_contra! hcon
  exact frame_1_1.not_valid_axiomM hab (LogicECKD.sound frame_1_1 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicECKD α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicECKD.sound frame_1_0 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECKD α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomT (LogicECKD.sound frame_2_140 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicECKD α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicECKD.sound frame_1_0 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicECKD α) := by
  intro hcon
  exact frame_1_1.not_valid_axiomP (LogicECKD.sound frame_1_1 hcon)

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicECKD α) := by
  by_contra! hcon
  exact frame_1_1.not_valid_axiomFour (LogicECKD.sound frame_1_1 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicECKD α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicECKD.sound frame_1_0 (hcon #a))

end LogicECKD

end
