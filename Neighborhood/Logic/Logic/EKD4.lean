module

public import Neighborhood.Logic.Logic.EKD
public import Neighborhood.Logic.Logic.EK4
public import Neighborhood.Logic.Logic.ED4
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_90
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame3_6

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEKD4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.HasPropertyK] [F.IsSerial]
    [F.IsTransitive] :
    A ∈ LogicEKD4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEKD4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEKD4.sound frame_1_2 hC⟩

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEKD4 α) := by
  by_contra! hcon
  exact frame_2_90.not_valid_axiomM hab (LogicEKD4.sound frame_2_90 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEKD4 α) := by
  by_contra! hcon
  exact frame_3_6.not_valid_axiomC hab (LogicEKD4.sound frame_3_6 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEKD4 α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEKD4.sound frame_1_0 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEKD4 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicEKD4.sound frame_2_170 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEKD4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEKD4.sound frame_1_0 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEKD4 α) := by
  intro hcon
  exact frame_2_90.not_valid_axiomP (LogicEKD4.sound frame_2_90 hcon)

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEKD4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEKD4.sound frame_1_0 (hcon #a))

end LogicEKD4

end
