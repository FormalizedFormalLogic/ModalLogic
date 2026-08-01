module

public import Neighborhood.Logic.Logic.EK
public import Neighborhood.Logic.Logic.EB
public import Neighborhood.Semantics.Example.Frame1_1
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_140
public import Neighborhood.Semantics.Example.Frame3_2359090

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEKB

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.HasPropertyK] [F.IsSymmetric] :
    A ∈ LogicEKB → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEKB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEKB.sound frame_1_2 hC⟩

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEKB α) := by
  by_contra! hcon
  exact frame_1_1.not_valid_axiomM hab (LogicEKB.sound frame_1_1 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEKB α) := by
  by_contra! hcon
  exact frame_3_2359090.not_valid_axiomC hab (LogicEKB.sound frame_3_2359090 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEKB α) := by
  intro hcon
  exact frame_1_1.not_valid_axiomN (LogicEKB.sound frame_1_1 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEKB α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEKB.sound frame_1_3 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEKB α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEKB.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEKB α) := by
  intro hcon
  exact frame_1_1.not_valid_axiomP (LogicEKB.sound frame_1_1 hcon)

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEKB α) := by
  by_contra! hcon
  exact frame_1_1.not_valid_axiomFour (LogicEKB.sound frame_1_1 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEKB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFive (LogicEKB.sound frame_2_140 (hcon #a))

end LogicEKB

end
