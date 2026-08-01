module

public import Neighborhood.Logic.Logic.ECK
public import Neighborhood.Logic.Logic.ECP
public import Neighborhood.Logic.Logic.EKP
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_8
public import Neighborhood.Semantics.Example.Frame2_34

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECKP

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.HasPropertyK]
    [F.NotContainsEmpty] :
    A ∈ LogicECKP → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) <;> simp)

instance : (@LogicECKP α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECKP.sound frame_1_2 hC⟩

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECKP α) := by
  by_contra! hcon
  exact frame_2_34.not_valid_axiomM hab (LogicECKP.sound frame_2_34 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicECKP α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicECKP.sound frame_1_0 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECKP α) := by
  by_contra! hcon
  exact frame_2_34.not_valid_axiomT (LogicECKP.sound frame_2_34 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicECKP α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicECKP.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicECKP α) := by
  by_contra! hcon
  exact frame_2_8.not_valid_axiomFour (LogicECKP.sound frame_2_8 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicECKP α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicECKP.sound frame_1_0 (hcon #a))

end LogicECKP

end
