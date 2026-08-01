module

public import Neighborhood.Logic.Logic.EKD
public import Neighborhood.Logic.Logic.EK5
public import Neighborhood.Logic.Logic.ED5
public import Neighborhood.Semantics.Example.Frame2_90
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame3_10529440

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEKD5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.HasPropertyK] [F.IsSerial]
    [F.IsEuclidean] :
    A ∈ LogicEKD5 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEKD5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEKD5.sound frame_1_2 hC⟩

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEKD5 α) := by
  by_contra! hcon
  exact frame_2_90.not_valid_axiomM hab (LogicEKD5.sound frame_2_90 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEKD5 α) := by
  intro hcon
  exact frame_2_90.not_valid_axiomN (LogicEKD5.sound frame_2_90 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEKD5 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicEKD5.sound frame_2_170 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEKD5 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicEKD5.sound frame_2_170 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEKD5 α) := by
  intro hcon
  exact frame_2_90.not_valid_axiomP (LogicEKD5.sound frame_2_90 hcon)

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEKD5 α) := by
  by_contra! hcon
  exact frame_3_10529440.not_valid_axiomFour (LogicEKD5.sound frame_3_10529440 (hcon #a))

end LogicEKD5

end
