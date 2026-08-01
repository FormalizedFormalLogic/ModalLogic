module

public import Neighborhood.Logic.Logic.ECK
public import Neighborhood.Logic.Logic.EC5
public import Neighborhood.Logic.Logic.EK5
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_79
public import Neighborhood.Semantics.Example.Frame2_90
public import Neighborhood.Semantics.Example.Frame2_170

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECK5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.HasPropertyK] [F.IsEuclidean] :
    A ∈ LogicECK5 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECK5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECK5.sound frame_1_2 hC⟩

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECK5 α) := by
  by_contra! hcon
  exact frame_2_79.not_valid_axiomM hab (LogicECK5.sound frame_2_79 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicECK5 α) := by
  intro hcon
  exact frame_2_90.not_valid_axiomN (LogicECK5.sound frame_2_90 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECK5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicECK5.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicECK5 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicECK5.sound frame_2_170 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicECK5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicECK5.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicECK5 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicECK5.sound frame_1_3 hcon)

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicECK5 α) := by
  by_contra! hcon
  exact frame_2_79.not_valid_axiomFour (LogicECK5.sound frame_2_79 (hcon #a))

end LogicECK5

end
