module

public import Neighborhood.Logic.Logic.ECK
public import Neighborhood.Logic.Logic.ECB
public import Neighborhood.Logic.Logic.EKB
public import Neighborhood.Semantics.Example.Frame1_1
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_140

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECKB

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.HasPropertyK] [F.IsSymmetric] :
    A ∈ LogicECKB → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECKB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECKB.sound frame_1_2 hC⟩

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECKB α) := by
  by_contra! hcon
  exact frame_1_1.not_valid_axiomM hab (LogicECKB.sound frame_1_1 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicECKB α) := by
  intro hcon
  exact frame_1_1.not_valid_axiomN (LogicECKB.sound frame_1_1 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECKB α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicECKB.sound frame_1_3 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicECKB α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicECKB.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicECKB α) := by
  intro hcon
  exact frame_1_1.not_valid_axiomP (LogicECKB.sound frame_1_1 hcon)

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicECKB α) := by
  by_contra! hcon
  exact frame_1_1.not_valid_axiomFour (LogicECKB.sound frame_1_1 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicECKB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFive (LogicECKB.sound frame_2_140 (hcon #a))

end LogicECKB

end
