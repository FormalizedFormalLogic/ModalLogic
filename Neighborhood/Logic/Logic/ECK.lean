module

public import Neighborhood.Logic.Logic.EC
public import Neighborhood.Logic.Logic.EK
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame1_1
public import Neighborhood.Semantics.Example.Frame1_3

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECK

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.HasPropertyK] :
    A ∈ LogicECK → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) <;> simp)

instance : (@LogicECK α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECK.sound frame_1_2 hC⟩

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECK α) := by
  by_contra! hcon
  exact frame_1_1.not_valid_axiomM hab (LogicECK.sound frame_1_1 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicECK α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicECK.sound frame_1_0 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECK α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicECK.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicECK α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicECK.sound frame_1_0 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicECK α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicECK.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicECK α) := by
  intro hcon
  exact frame_1_1.not_valid_axiomP (LogicECK.sound frame_1_1 hcon)

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicECK α) := by
  by_contra! hcon
  exact frame_1_1.not_valid_axiomFour (LogicECK.sound frame_1_1 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicECK α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicECK.sound frame_1_0 (hcon #a))

end LogicECK

end
