module

public import Neighborhood.Logic.Logic.ECP
public import Neighborhood.Logic.Logic.EC5
public import Neighborhood.Logic.Logic.EP5
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame3_8553090
public import Neighborhood.Semantics.Example.Frame3_10529440

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECP5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.NotContainsEmpty]
    [F.IsEuclidean] :
    A ∈ LogicECP5 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECP5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECP5.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicECP5 α) := by
  by_contra! hcon
  exact frame_3_8553090.not_valid_axiomK hab (LogicECP5.sound frame_3_8553090 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECP5 α) := by
  by_contra! hcon
  exact frame_3_8553090.not_valid_axiomM hab (LogicECP5.sound frame_3_8553090 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECP5 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicECP5.sound frame_2_170 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicECP5 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicECP5.sound frame_2_170 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicECP5 α) := by
  by_contra! hcon
  exact frame_3_10529440.not_valid_axiomFour (LogicECP5.sound frame_3_10529440 (hcon #a))

end LogicECP5

end
