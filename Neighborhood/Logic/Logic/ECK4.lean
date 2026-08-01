module

public import Neighborhood.Logic.Logic.ECK
public import Neighborhood.Logic.Logic.EC4
public import Neighborhood.Logic.Logic.EK4
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_90

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECK4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.HasPropertyK] [F.IsTransitive] :
    A ∈ LogicECK4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECK4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECK4.sound frame_1_2 hC⟩

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECK4 α) := by
  by_contra! hcon
  exact frame_2_90.not_valid_axiomM hab (LogicECK4.sound frame_2_90 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicECK4 α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicECK4.sound frame_1_0 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECK4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicECK4.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicECK4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicECK4.sound frame_1_0 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicECK4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicECK4.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicECK4 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicECK4.sound frame_1_3 hcon)

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicECK4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicECK4.sound frame_1_0 (hcon #a))

end LogicECK4

end
