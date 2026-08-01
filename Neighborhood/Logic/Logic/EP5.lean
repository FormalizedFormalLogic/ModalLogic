module

public import Neighborhood.Logic.Logic.EP
public import Neighborhood.Logic.Logic.E5
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame2_206
public import Neighborhood.Semantics.Example.Frame3_8553090
public import Neighborhood.Semantics.Example.Frame3_10528928

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEP5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.NotContainsEmpty] [F.IsEuclidean] :
    A ∈ LogicEP5 → F ⊧ A :=
  Hilbert.sound (by rintro _ (rfl | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEP5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEP5.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEP5 α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomK hab (LogicEP5.sound frame_2_206 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEP5 α) := by
  by_contra! hcon
  exact frame_3_8553090.not_valid_axiomM hab (LogicEP5.sound frame_3_8553090 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEP5 α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomC hab (LogicEP5.sound frame_2_206 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEP5 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicEP5.sound frame_2_170 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEP5 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicEP5.sound frame_2_170 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEP5 α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomD (LogicEP5.sound frame_2_206 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEP5 α) := by
  by_contra! hcon
  exact frame_3_10528928.not_valid_axiomFour (LogicEP5.sound frame_3_10528928 (hcon #a))

end LogicEP5

end
