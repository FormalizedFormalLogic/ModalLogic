module

public import Neighborhood.Logic.Logic.ECK
public import Neighborhood.Logic.Logic.ECT
public import Neighborhood.Logic.Logic.EKT
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_8
public import Neighborhood.Semantics.Example.Frame2_72

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECKT

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.HasPropertyK]
    [F.IsReflexive] :
    A ∈ LogicECKT → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECKT α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECKT.sound frame_1_2 hC⟩

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECKT α) := by
  by_contra! hcon
  exact frame_2_72.not_valid_axiomM hab (LogicECKT.sound frame_2_72 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicECKT α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicECKT.sound frame_1_0 hcon)

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicECKT α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicECKT.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicECKT α) := by
  by_contra! hcon
  exact frame_2_8.not_valid_axiomFour (LogicECKT.sound frame_2_8 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicECKT α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicECKT.sound frame_1_0 (hcon #a))

end LogicECKT

end
