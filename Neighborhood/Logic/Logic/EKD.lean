module

public import Neighborhood.Logic.Logic.EK
public import Neighborhood.Logic.Logic.ED
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame1_1
public import Neighborhood.Semantics.Example.Frame2_140
public import Neighborhood.Semantics.Example.Frame4_11259170869739560

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEKD

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.HasPropertyK] [F.IsSerial] :
    A ∈ LogicEKD → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEKD α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEKD.sound frame_1_2 hC⟩

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEKD α) := by
  by_contra! hcon
  exact frame_1_1.not_valid_axiomM hab (LogicEKD.sound frame_1_1 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEKD α) := by
  by_contra! hcon
  exact frame_4_11259170869739560.not_valid_axiomC hab (LogicEKD.sound frame_4_11259170869739560 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEKD α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEKD.sound frame_1_0 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEKD α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomT (LogicEKD.sound frame_2_140 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEKD α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEKD.sound frame_1_0 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEKD α) := by
  intro hcon
  exact frame_1_1.not_valid_axiomP (LogicEKD.sound frame_1_1 hcon)

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEKD α) := by
  by_contra! hcon
  exact frame_1_1.not_valid_axiomFour (LogicEKD.sound frame_1_1 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEKD α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEKD.sound frame_1_0 (hcon #a))

end LogicEKD

end
