module

public import Neighborhood.Logic.Logic.EDP
public import Neighborhood.Logic.Logic.ED4
public import Neighborhood.Logic.Logic.EP4
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame3_6
public import Neighborhood.Semantics.Example.Frame3_43176

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEDP4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsSerial] [F.NotContainsEmpty] [F.IsTransitive] :
    A ∈ LogicEDP4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEDP4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEDP4.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEDP4 α) := by
  by_contra! hcon
  exact frame_3_43176.not_valid_axiomK hab (LogicEDP4.sound frame_3_43176 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEDP4 α) := by
  by_contra! hcon
  exact frame_3_6.not_valid_axiomM hab (LogicEDP4.sound frame_3_6 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEDP4 α) := by
  by_contra! hcon
  exact frame_3_6.not_valid_axiomC hab (LogicEDP4.sound frame_3_6 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEDP4 α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEDP4.sound frame_1_0 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEDP4 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicEDP4.sound frame_2_170 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEDP4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEDP4.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEDP4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEDP4.sound frame_1_0 (hcon #a))

end LogicEDP4

end
