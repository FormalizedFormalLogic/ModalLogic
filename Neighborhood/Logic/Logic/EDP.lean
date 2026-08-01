module

public import Neighborhood.Logic.Logic.ED
public import Neighborhood.Logic.Logic.EP
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_8
public import Neighborhood.Semantics.Example.Frame2_140
public import Neighborhood.Semantics.Example.Frame3_43176
public import Neighborhood.Semantics.Example.Frame3_8553090

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEDP

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsSerial] [F.NotContainsEmpty] :
    A ∈ LogicEDP → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, rfl⟩ | rfl) <;> simp)

instance : (@LogicEDP α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEDP.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEDP α) := by
  by_contra! hcon
  exact frame_3_43176.not_valid_axiomK hab (LogicEDP.sound frame_3_43176 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEDP α) := by
  by_contra! hcon
  exact frame_3_8553090.not_valid_axiomM hab (LogicEDP.sound frame_3_8553090 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEDP α) := by
  by_contra! hcon
  exact frame_3_43176.not_valid_axiomC hab (LogicEDP.sound frame_3_43176 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEDP α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEDP.sound frame_1_0 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEDP α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomT (LogicEDP.sound frame_2_140 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEDP α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEDP.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEDP α) := by
  by_contra! hcon
  exact frame_2_8.not_valid_axiomFour (LogicEDP.sound frame_2_8 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEDP α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEDP.sound frame_1_0 (hcon #a))

end LogicEDP

end
