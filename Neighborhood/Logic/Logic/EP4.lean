module

public import Neighborhood.Logic.Logic.EP
public import Neighborhood.Logic.Logic.E4
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame2_206
public import Neighborhood.Semantics.Example.Frame3_8553090

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEP4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.NotContainsEmpty] [F.IsTransitive] :
    A ∈ LogicEP4 → F ⊧ A :=
  Hilbert.sound (by rintro _ (rfl | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEP4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEP4.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEP4 α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomK hab (LogicEP4.sound frame_2_206 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEP4 α) := by
  by_contra! hcon
  exact frame_3_8553090.not_valid_axiomM hab (LogicEP4.sound frame_3_8553090 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEP4 α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomC hab (LogicEP4.sound frame_2_206 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEP4 α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEP4.sound frame_1_0 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEP4 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicEP4.sound frame_2_170 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEP4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEP4.sound frame_1_0 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEP4 α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomD (LogicEP4.sound frame_2_206 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEP4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEP4.sound frame_1_0 (hcon #a))

end LogicEP4

end
