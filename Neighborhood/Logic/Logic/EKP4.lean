module

public import Neighborhood.Logic.Logic.EKP
public import Neighborhood.Logic.Logic.EK4
public import Neighborhood.Logic.Logic.EP4
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame3_6

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEKP4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.HasPropertyK] [F.NotContainsEmpty]
    [F.IsTransitive] :
    A ∈ LogicEKP4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEKP4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEKP4.sound frame_1_2 hC⟩

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEKP4 α) := by
  by_contra! hcon
  exact frame_3_6.not_valid_axiomM hab (LogicEKP4.sound frame_3_6 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEKP4 α) := by
  by_contra! hcon
  exact frame_3_6.not_valid_axiomC hab (LogicEKP4.sound frame_3_6 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEKP4 α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEKP4.sound frame_1_0 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEKP4 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicEKP4.sound frame_2_170 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEKP4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEKP4.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEKP4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEKP4.sound frame_1_0 (hcon #a))

end LogicEKP4

end
